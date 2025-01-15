from dataclasses import dataclass
from dataclasses import dataclass

from typing import Dict, List, Optional, Tuple
import re
from dataclasses import dataclass
from verifier import (
    Point, Line, Angle, GeometricFact, GeometricState, AngleStatement,
    SymbolicExpression, makePoint, makeLine, makeAngle,
    quadrilateralAngleSumTheorem, adjacentComplementaryAngleTheorem,
    parallelogramOppositeAngleTheorem, parallelAlternateInteriorAnglesTheorem,
    angleAdditionTheorem, propagateEqualAngles, applyGeometricTheoremWithErrors,
    ErrorTier, GeometricError, points_equal_with_rotations
)



class ParsedTheorem:
    def __init__(self, name: str, points: List[str], premise: str, conclusion: List[str]):
        self.name = name
        self.points = points
        self.premise = premise
        self.conclusion = conclusion

    def __repr__(self):
        return f"ParsedTheorem(name='{self.name}', points={self.points}, premise='{self.premise}')"

class ParserError(Exception):
    """Base class for parser errors"""

    def __init__(self, message: str, tier: int):
        self.message = message
        self.tier = tier
        super().__init__(self.message)




def is_valid_parallelogram_ordering(points_str: str) -> bool:
    """
    Check if a parallelogram point ordering is valid (cyclic rotation only).
    ABCD, BCDA, CDAB, DABC are valid
    ABDC, ADCB, etc. are invalid
    """
    # Get base parallelogram orderings
    A, B, C, D = points_str[0], points_str[1], points_str[2], points_str[3]
    valid_orderings = [A+B+C+D, B+C+D+A, C+D+A+B, D+A+B+C]
    return points_str in valid_orderings

def extract_section(content: str, start_marker: str, end_marker: str) -> str:
    """Extract a section from the content between markers"""
    # First remove sections we want to ignore
    ignore_sections = ["SYMBOLS_AND_VALUES:", "EQUATIONS:"]
    clean_content = content
    for section in ignore_sections:
        clean_content = re.sub(f"{section}.*?(?=(CONSTRUCTION|TEXT|GOAL|ANSWER|THEOREM)_CDL:)",
                               "", clean_content, flags=re.DOTALL)

    # Then extract the section we want
    pattern = f"{start_marker}(.*?){end_marker}"
    match = re.search(pattern, clean_content, re.DOTALL)
    return match.group(1).strip() if match else ""


def parse_angle_statement(statement: str, points_dict: Dict[str, Point]) -> Optional[AngleStatement]:
    """Parse angle statements like 'Equal(MeasureOfAngle(ABC),40)' or 'Equal(MeasureOfAngle(ABC),a+2)'"""
    angle_match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', statement)
    if not angle_match:
        return None

    angle_points = angle_match.group(1)
    measure_str = angle_match.group(2).strip()

    if len(angle_points) != 3:
        return None

    try:
        p1 = points_dict[angle_points[0]]
        v = points_dict[angle_points[1]]
        p2 = points_dict[angle_points[2]]
        angle = makeAngle(p1, v, p2)

        # Handle both numeric and symbolic measures
        measure = float(measure_str) if measure_str.replace('.', '').isdigit() else measure_str
        return AngleStatement(angle, measure)
    except KeyError as e:
        missing_point = str(e.args[0])
        raise ParserError(f"Point {missing_point} referenced in angle {angle_points} but does not exist", 1)
    except ValueError:
        return AngleStatement(angle, measure_str)


def parse_theorem_sequence(sequence: str) -> List[ParsedTheorem]:
    """Parse theorem sequence into structured format"""
    theorems = []

    # Handle both formats
    if 'step_id:' in sequence.lower():
        # Format 1: step_id: 1; theorem: name(args)...
        parts = sequence.split('step_id:')
        for part in parts:
            if not part.strip():
                continue

            if 'theorem:' in part.lower():
                theorem_part = part.split('theorem:', 1)[1].split('premise:', 1)[0].strip()
                match = re.match(r'(\w+)\((.*?)\)', theorem_part)
                if match:
                    name = match.group(1)
                    args = [arg.strip() for arg in match.group(2).split(',')]

                    premise = ''
                    if 'premise:' in part.lower():
                        premise = part.split('premise:', 1)[1].split('conclusion:', 1)[0].strip()

                    conclusion = []
                    if 'conclusion:' in part.lower():
                        conclusion_str = part.split('conclusion:', 1)[1].strip()
                        try:
                            conclusion = eval(conclusion_str)
                        except:
                            conclusion = []

                    theorems.append(ParsedTheorem(name=name, points=args,
                                                  premise=premise, conclusion=conclusion))

    elif 'Step' in sequence:
        # Format 2: Step 1: Theorem: name(args)...
        steps = sequence.split('Step')
        for step in steps:
            if not step.strip():
                continue

            # Split into lines and clean up
            lines = [line.strip() for line in step.split('\n') if line.strip()]

            theorem_line = next((line for line in lines if 'Theorem:' in line), None)
            if theorem_line:
                # Extract theorem name and args
                theorem_part = theorem_line.split('Theorem:', 1)[1].strip()
                match = re.match(r'(\w+)\((.*?)\)', theorem_part)
                if match:
                    name = match.group(1)
                    args = [arg.strip() for arg in match.group(2).split(',')]

                    # Get premise and conclusion
                    premise = ''
                    conclusion = []

                    for line in lines:
                        if 'Premise:' in line:
                            premise = line.split('Premise:', 1)[1].strip()
                        elif 'Conclusion:' in line:
                            try:
                                conclusion_str = line.split('Conclusion:', 1)[1].strip()
                                conclusion = eval(conclusion_str)
                            except:
                                conclusion = []

                    theorems.append(ParsedTheorem(name=name, points=args,
                                                  premise=premise, conclusion=conclusion))

    print(f"\nParsed theorems:")
    for t in theorems:
        print(f"• {t.name}({', '.join(t.points)})")

    return theorems


def create_initial_state(content: str) -> Tuple[GeometricState, Dict[str, Point]]:
    """Create initial geometric state from proof file content"""
    points_dict: Dict[str, Point] = {}
    initial_facts: List[GeometricFact] = []
    initial_angles: List[AngleStatement] = []

    try:
        # First pass: collect all point declarations
        construction = extract_section(content, "CONSTRUCTION_CDL_EXTENDED:", "SYMBOLS_AND_VALUES:")
        for line in construction.split('\n'):
            line = line.strip()
            if line.startswith('Point('):
                point_name = line[6:-1]
                points_dict[point_name] = makePoint(point_name)

        # Second pass: validate all geometric structures
        # Validate Shape/Polygon points
        construction = extract_section(content, "CONSTRUCTION_CDL_EXTENDED:", "SYMBOLS_AND_VALUES:")
        for line in construction.split('\n'):
            line = line.strip()
            if line.startswith('Polygon('):
                points_str = line[8:-1]
                for point_name in points_str:
                    if point_name not in points_dict:
                        raise ParserError(
                            f"Point {point_name} referenced in polygon but not declared. Available points: {list(points_dict.keys())}",
                            1
                        )
                polygon_points = create_points_from_shape(line[8:-1], points_dict)
                if polygon_points:
                    point_set = set(polygon_points)
                    if not any(set(fact.points) == point_set for fact in initial_facts if fact.type == "Shape"):
                        initial_facts.append(GeometricFact(type_="Shape", points=polygon_points))

        # Validate Collinear points
        construction = extract_section(content, "CONSTRUCTION_CDL:", "TEXT_CDL:")
        for line in construction.split('\n'):
            line = line.strip()
            if not line:
                continue

            if line.startswith('Collinear('):
                points_str = line[10:-1]
                for point_name in points_str:
                    if point_name not in points_dict:
                        raise ParserError(
                            f"Point {point_name} referenced in collinear statement but not declared. Available points: {list(points_dict.keys())}",
                            1
                        )
                collinear_points = [points_dict[p] for p in points_str if p in points_dict]
                if len(collinear_points) >= 2:
                    initial_facts.append(GeometricFact(type_="Collinear", points=collinear_points))

        # Parse text statements and validate all referenced points
        text_cdl = extract_section(content, "TEXT_CDL:", "GOAL_CDL:")
        for line in text_cdl.split('\n'):
            line = line.strip()
            if not line:
                continue

            if line.startswith('Parallelogram('):
                points_str = line[14:-1]

                # Validate order first
                if not is_valid_parallelogram_ordering(points_str):
                    # Find existing parallelogram for valid orderings
                    base_points = 'ABCD'  # Default if no parallelogram exists
                    for fact in initial_facts:
                        if fact.type == "Parallelogram":
                            base_points = ''.join(p.name for p in fact.points)
                            break
                    valid_orders = [base_points[i:] + base_points[:i] for i in range(4)]
                    raise ParserError(
                        f"Invalid parallelogram ordering '{points_str}'. Must be a cyclic rotation. "
                        f"Valid orderings are: {valid_orders}", 1)

                # Then check points exist
                for point_name in points_str:
                    if point_name not in points_dict:
                        raise ParserError(
                            f"Point {point_name} referenced in parallelogram but not declared. Available points: {list(points_dict.keys())}",
                            1
                        )
                para_points = create_points_from_shape(points_str, points_dict)
                if para_points:
                    initial_facts.append(GeometricFact(type_="Parallelogram", points=para_points))

            elif line.startswith('Equal(MeasureOfAngle('):
                angle_match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                if angle_match:
                    angle_points = angle_match.group(1)
                    for point_name in angle_points:
                        if point_name not in points_dict:
                            raise ParserError(
                                f"Point {point_name} referenced in angle statement but not declared. Available points: {list(points_dict.keys())}",
                                1
                            )
                angle_stmt = parse_angle_statement(line, points_dict)
                if angle_stmt:
                    initial_angles.append(angle_stmt)

            elif line.startswith('ParallelBetweenLine('):
                points_str = line[19:-1]
                pairs = points_str.split(',')
                if len(pairs) == 2:
                    pair1 = pairs[0].strip().replace('(', '').replace(')', '')
                    pair2 = pairs[1].strip().replace('(', '').replace(')', '')
                    for point_name in pair1 + pair2:
                        if point_name not in points_dict:
                            raise ParserError(
                                f"Point {point_name} referenced in parallel lines but not declared. Available points: {list(points_dict.keys())}",
                                1
                            )
                    line1_pts = [points_dict[p] for p in pair1]
                    line2_pts = [points_dict[p] for p in pair2]
                    line1 = makeLine(line1_pts[0], line1_pts[1])
                    line2 = makeLine(line2_pts[0], line2_pts[1])
                    initial_facts.append(GeometricFact(type_="Parallel", lines=[line1, line2]))

            elif line.startswith('PerpendicularBetweenLine('):
                points_str = line[24:-1]
                pairs = points_str.split(',')
                if len(pairs) == 2:
                    pair1 = pairs[0].strip().replace('(', '').replace(')', '')
                    pair2 = pairs[1].strip().replace('(', '').replace(')', '')
                    for point_name in pair1 + pair2:
                        if point_name not in points_dict:
                            raise ParserError(
                                f"Point {point_name} referenced in perpendicular lines but not declared. Available points: {list(points_dict.keys())}",
                                1
                            )
                    line1_pts = [points_dict[p] for p in pair1]
                    line2_pts = [points_dict[p] for p in pair2]
                    p1 = points_dict[pair1[0]]
                    v = points_dict[pair1[1]]
                    p2 = points_dict[pair2[0]]
                    perp_angle = makeAngle(p1, v, p2)
                    initial_angles.append(AngleStatement(perp_angle, 90.0))

        return GeometricState(facts=initial_facts, angles=initial_angles), points_dict

    except ParserError as e:
        raise e
    except KeyError as e:
        missing_point = str(e.args[0])
        raise ParserError(
            f"Point {missing_point} referenced but not declared. Available points: {list(points_dict.keys())}", 1)
    except Exception as e:
        raise ParserError(f"Error creating initial state: {str(e)}", 1)


def setup_theorem_points_and_angles(theorem: ParsedTheorem,
                                    points_dict: Dict[str, Point],
                                    state: GeometricState) -> Tuple[List[Point], List[Line], List[Angle]]:
    """Set up points and angles for theorem application based on theorem type"""
    print("\nAvailable angles in state:")
    for angle_stmt in state.angles:
        print(f"• {angle_stmt}")

    points = []
    lines = []
    angles = []

    print(f"\nTheorem type: {theorem.name}")
    print(f"Theorem points: {theorem.points}")

    if theorem.name == 'parallelogram_property_opposite_angle_equal':
        points = []
        angles = []
        para_points_str = next((arg for arg in theorem.points if len(arg) == 4), None)

        if not para_points_str:
            raise ParserError("Parallelogram theorem requires a 4-point sequence", 1)

        # Validate ordering
        if not is_valid_parallelogram_ordering(para_points_str):
            # Find the existing parallelogram for valid orderings
            found_fact = None
            for fact in state.facts:
                if fact.type == "Parallelogram":
                    found_fact = fact
                    base_points = ''.join(p.name for p in fact.points)
                    valid_orders = [base_points[i:] + base_points[:i] for i in range(4)]
                    raise ParserError(
                        f"Invalid parallelogram ordering '{para_points_str}'. Must be a cyclic rotation. "
                        f"Valid orderings are: {valid_orders}", 1)

        try:
            # Create points while maintaining order
            para_points = [points_dict[p] for p in para_points_str]

            # Find matching parallelogram fact
            found_fact = None
            for fact in state.facts:
                if fact.type == "Parallelogram":
                    if points_equal_with_rotations(fact.points, para_points, "Parallelogram"):
                        found_fact = fact
                        break

            if found_fact:
                # Use points from the fact to maintain consistent ordering
                points = found_fact.points
                p1 = points[3]  # D
                v1 = points[0]  # A
                p2 = points[1]  # B
                angle1 = makeAngle(p1, v1, p2)  # DAB

                p3 = points[1]  # B
                v2 = points[2]  # C
                p4 = points[3]  # D
                angle2 = makeAngle(p3, v2, p4)  # BCD

                angles = [angle1, angle2]

        except KeyError as e:
            missing_point = str(e.args[0])
            raise ParserError(
                f"Point {missing_point} referenced but not declared. Available points: {list(points_dict.keys())}", 1)

        print(f"Setting up parallelogram with points: {[p.name for p in points]}")
        print(f"And angles: {[f'∠{a.point1.name}{a.vertex.name}{a.point2.name}' for a in angles]}")

    # [Rest of the function remains unchanged]
    elif theorem.name == 'parallel_property_alternate_interior_angle':
        line_points = [pt for pt in theorem.points if len(pt) == 2]  # Get just the 2-letter line points
        print(f"Processing parallel lines: {line_points}")

        if len(line_points) >= 2:
            line1, line2 = line_points[0], line_points[1]  # CD, AB

            print(f"Creating alternate interior angles between {line1} and {line2}")

            try:
                # Create lines and points
                line1_pts = [points_dict[line1[0]], points_dict[line1[1]]]  # C,D
                line2_pts = [points_dict[line2[0]], points_dict[line2[1]]]  # A,B

                lines = [makeLine(line1_pts[0], line1_pts[1]),
                         makeLine(line2_pts[0], line2_pts[1])]

                # For CD||AB, we create angle DCB and ABC
                angle1 = makeAngle(line1_pts[1],  # D
                                   line1_pts[0],  # C
                                   points_dict['B'])  # B

                angle2 = makeAngle(line2_pts[0],  # A
                                   line2_pts[1],  # B
                                   points_dict['C'])  # C

                angles = [angle1, angle2]
                points = line1_pts + line2_pts

                print(
                    f"Created angles: ∠{angle1.point1.name}{angle1.vertex.name}{angle1.point2.name} and ∠{angle2.point1.name}{angle2.vertex.name}{angle2.point2.name}")
            except KeyError as e:
                missing_point = str(e.args[0])
                raise ParserError(f"Point {missing_point} does not exist but is referenced in parallel lines theorem",
                                  1)

    elif theorem.name == 'angle_addition':
        angle_points = [pt for pt in theorem.points if len(pt) == 3]
        print(f"Processing angle addition angles: {angle_points}")

        if len(angle_points) >= 2:
            try:
                angle1_name = angle_points[0]
                angle2_name = angle_points[1]

                v = points_dict[angle1_name[1]]  # Common vertex
                total_angle = makeAngle(
                    points_dict[angle1_name[0]],  # E
                    v,  # C
                    points_dict[angle2_name[2]]  # B
                )

                known_angle = makeAngle(
                    points_dict[angle2_name[0]],  # D
                    v,  # C
                    points_dict[angle2_name[2]]  # B
                )

                target_angle = makeAngle(
                    points_dict[angle1_name[0]],  # E
                    v,  # C
                    points_dict[angle1_name[2]]  # D
                )

                angles = [total_angle, target_angle, known_angle]
                points = [
                    points_dict[angle1_name[0]],
                    v,
                    points_dict[angle1_name[2]],
                    points_dict[angle2_name[2]]
                ]
            except KeyError as e:
                missing_point = str(e.args[0])
                raise ParserError(f"Point {missing_point} does not exist but is referenced in angle addition theorem",
                                  1)

            for ang in angles:
                existing_stmt = next((stmt for stmt in state.angles if stmt.angle == ang), None)
                if existing_stmt is None:
                    state.angles.append(AngleStatement(ang, None))

    elif theorem.name == 'quadrilateral_property_angle_sum':
        # Get the quadrilateral points from the argument
        points = []
        angles = []
        quad_points_str = next((arg for arg in theorem.points if len(arg) == 4), None)
        if quad_points_str:
            try:
                quad_points = [points_dict[p] for p in quad_points_str]
                points.extend(quad_points)

                # For quadrilateral_property_angle_sum, gather all angles in the state that match
                for angle_stmt in state.angles:
                    angle = angle_stmt.angle
                    if (angle.vertex in quad_points and
                            angle.point1 in quad_points and
                            angle.point2 in quad_points):
                        if angle not in angles:
                            angles.append(angle)
            except KeyError as e:
                missing_point = str(e.args[0])
                raise ParserError(f"Point {missing_point} does not exist but is referenced in quadrilateral theorem", 1)

        print(f"Found {len(angles)} angles in quadrilateral")

    elif theorem.name == 'adjacent_complementary_angle':
        print(f"Processing adjacent complementary angles: {theorem.points}")

        angle_points = [pt for pt in theorem.points if len(pt) == 3]  # e.g. 'ECB', 'BCA'
        if len(angle_points) >= 2:
            try:
                point_names1 = angle_points[0]  # 'ECB'
                point_names2 = angle_points[1]  # 'BCA'

                print(f"Using angles: {point_names1} and {point_names2}")

                p1 = points_dict[point_names1[0]]  # E
                v = points_dict[point_names1[1]]  # C
                p2 = points_dict[point_names1[2]]  # B
                p3 = points_dict[point_names2[2]]  # A

                points = [p1, v, p3]
                angles = [
                    makeAngle(p1, v, p2),  # ECB
                    makeAngle(p2, v, p3)  # BCA
                ]
            except KeyError as e:
                missing_point = str(e.args[0])
                raise ParserError(
                    f"Point {missing_point} does not exist but is referenced in adjacent complementary angle theorem",
                    1)

    for ang in angles:
        existing_stmt = next((stmt for stmt in state.angles if stmt.angle == ang), None)
        if existing_stmt is None:
            state.angles.append(AngleStatement(ang, None))

    return points, lines, angles







def apply_theorem_sequence(state: GeometricState,
                         theorems: List[ParsedTheorem],
                         points_dict: Dict[str, Point]) -> Tuple[Optional[GeometricState], Optional[GeometricError]]:
    """Apply sequence of theorems to initial state"""
    current_state = state

    theorem_map = {
        'quadrilateral_property_angle_sum': quadrilateralAngleSumTheorem,
        'adjacent_complementary_angle': adjacentComplementaryAngleTheorem,
        'parallelogram_property_opposite_angle': parallelogramOppositeAngleTheorem,
        'parallelogram_property_opposite_angle_equal': parallelogramOppositeAngleTheorem,
        'parallel_property_alternate_interior_angle': parallelAlternateInteriorAnglesTheorem,
        'angle_addition': angleAdditionTheorem
    }

    for theorem in theorems:
        if theorem.name not in theorem_map:
            return None, GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL,
                message=f"Unknown theorem: {theorem.name}"
            )

        # Get theorem rule and try to prepare points/angles
        try:
            # For parallelogram theorems, validate point ordering first
            if theorem.name == 'parallelogram_property_opposite_angle_equal':
                para_points_str = next((arg for arg in theorem.points if len(arg) == 4), None)
                if para_points_str:
                    if not is_valid_parallelogram_ordering(para_points_str):
                        found_fact = None
                        for fact in state.facts:
                            if fact.type == "Parallelogram":
                                found_fact = fact
                                break
                        if found_fact:
                            base_points = ''.join(p.name for p in found_fact.points)
                            valid_orders = [base_points[i:] + base_points[:i] for i in range(4)]
                            return None, GeometricError(
                                tier=ErrorTier.TIER1_THEOREM_CALL,
                                message=f"Invalid parallelogram ordering '{para_points_str}'. Must be a cyclic rotation.",
                                details=f"Valid orderings for this parallelogram are: {valid_orders}"
                            )

            # Get theorem rule and prepare points/angles
            rule = theorem_map[theorem.name]
            points, lines, angles = setup_theorem_points_and_angles(theorem, points_dict, current_state)

            # Debug prints
            print("\nApplying theorem:", theorem.name)
            print("Points:", [p.name for p in points])
            print("Angles:", [f"∠{a.point1.name}{a.vertex.name}{a.point2.name}" for a in angles])

            # Apply theorem
            result_state, error = applyGeometricTheoremWithErrors(
                rule,
                current_state,
                points,
                lines,
                angles
            )

            if result_state:
                print("After theorem application:")
                for angle in result_state.angles:
                    print(f"• {angle}")

            if error:
                return None, error

            # Propagate equalities
            current_state = propagateEqualAngles(result_state)

        except ParserError as e:
            return None, GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL,
                message=e.message,
                details=f"Available points: {list(points_dict.keys())}"
            )

    return current_state, None




def create_points_from_shape(shape_str: str, points_dict: Dict[str, Point]) -> List[Point]:
    """Create points from a shape string like "XW,WZ,ZY,YX" or "ABCD" """
    shape_str = shape_str.replace('(', '').replace(')', '').strip()

    # Case 1: comma-separated edges like "XW,WZ,ZY,YX"
    if ',' in shape_str:
        segments = shape_str.split(',')
        point_names = set()
        for segment in segments:
            if len(segment.strip()) >= 2:
                p1, p2 = segment.strip()[0], segment.strip()[1]
                point_names.update([p1, p2])
                if p1 not in points_dict:
                    points_dict[p1] = makePoint(p1)
                if p2 not in points_dict:
                    points_dict[p2] = makePoint(p2)
        return [points_dict[name] for name in sorted(point_names)]

    # Case 2: simple sequence like "ABCD"
    point_names = list(shape_str.strip())
    for name in point_names:
        if name not in points_dict:
            points_dict[name] = makePoint(name)
    return [points_dict[name] for name in point_names]


def verify_geometric_proof(filename: str) -> bool:
    """Main function to verify a geometric proof file"""
    try:
        # Read file content
        with open(filename, 'r') as file:
            content = file.read()

        # Create initial state
        initial_state, points_dict = create_initial_state(content)

        # Print initial state
        print("Initial State:")
        print("=============")
        for fact in initial_state.facts:
            print(f"• {fact}")
        for angle in initial_state.angles:
            print(f"• {angle}")
        print()

        # Parse and apply theorem sequence
        theorem_sequence = extract_section(content, "THEOREM_SEQUENCE:", "$")
        theorems = parse_theorem_sequence(theorem_sequence)
        final_state, error = apply_theorem_sequence(initial_state, theorems, points_dict)

        if error:
            print(f"\nError in Tier {error.tier.value}: {error.tier.name}")
            print("=" * 40)
            print(f"Message: {error.message}")
            if error.details:
                print(f"Details: {error.details}")
            return False

        # Verify goal
        goal_symbol = extract_section(content, "GOAL_SYMBOL:", "ANSWER:").strip()
        expected_answer = float(extract_section(content, "ANSWER:", "THEOREM_SEQUENCE:").strip())

        # Look for the goal angle in the final state
        if final_state:
            # Get target angle name from goal_symbol (e.g., 'ma_ecd' -> 'ECD')
            target_angle = goal_symbol.split('_')[-1].upper()
            print(f"\nLooking for angle {target_angle} = {expected_answer}°")
            print("Current angles:")

            found_target = False
            for angle_stmt in final_state.angles:
                angle_name = f"{angle_stmt.angle.point1.name}{angle_stmt.angle.vertex.name}{angle_stmt.angle.point2.name}"
                reverse_name = f"{angle_stmt.angle.point2.name}{angle_stmt.angle.vertex.name}{angle_stmt.angle.point1.name}"

                value = angle_stmt.measure.evaluate()
                if value is not None:
                    print(f"• ∠{angle_name} = {value}°")
                else:
                    print(f"• ∠{angle_name} = No value determined")

                # Check both angle orientations
                if angle_name == target_angle or reverse_name == target_angle:
                    found_target = True
                    if value is None:
                        print(f"\nError in Tier 3: TIER3_GOAL_NOT_REACHED")
                        print("=" * 40)
                        print(f"Message: Unable to determine value for goal angle {target_angle}")
                        print("Details: Theorem sequence is incomplete - not enough information to calculate the angle")
                        return False
                    elif abs(value - expected_answer) < 1e-10:
                        print(f"\nFinal Result:")
                        print(f"============")
                        print(f"∠{target_angle} = {value}° (Expected: {expected_answer}°)")
                        print(f"Verification: ✓ Successful")
                        return True
                    else:
                        print(f"\nError in Tier 3: TIER3_GOAL_NOT_REACHED")
                        print("=" * 40)
                        print(
                            f"Message: Calculated value for {target_angle} ({value}°) doesn't match expected value ({expected_answer}°)")
                        return False

            if not found_target:
                print(f"\nError in Tier 3: TIER3_GOAL_NOT_REACHED")
                print("=" * 40)
                print(f"Message: Goal angle {target_angle} not found in final state")
                return False

    except FileNotFoundError:
        print(f"\nError: File '{filename}' not found")
        return False
    except ParserError as e:
        print(f"\nError in Tier 1: TIER1_THEOREM_CALL")
        print("=" * 40)
        print(f"Message: {e.message}")
        return False
    except Exception as e:
        print(f"\nError in Tier 3: TIER3_GOAL_NOT_REACHED")
        print("=" * 40)
        print(f"Message: {str(e)}")
        return False



if __name__ == "__main__":
    result = verify_geometric_proof("/questions/question2/question2_12")
    print(f"Verification {'succeeded' if result else 'failed'}")


