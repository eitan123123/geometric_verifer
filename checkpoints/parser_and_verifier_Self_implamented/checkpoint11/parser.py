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


def is_valid_parallelogram_ordering(points_str: str, base_str: Optional[str] = None) -> bool:
    """
    Check if a parallelogram ordering is valid based on the base ordering.
    If base_str is provided, points_str must be a cyclic rotation of it.
    If no base_str, any 4-point sequence is valid (first definition).
    """
    if len(points_str) != 4:
        return False

    if base_str:
        # Must match a cyclic rotation of the base ordering
        rotations = [base_str[i:] + base_str[:i] for i in range(4)]
        return points_str in rotations

    return True
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

        # Parse text statements and validate all referenced points
        text_cdl = extract_section(content, "TEXT_CDL:", "GOAL_CDL:")
        for line in text_cdl.split('\n'):
            line = line.strip()
            if not line:
                continue

            if line.startswith('Collinear('):
                points_str = line[10:-1]
                # Validate points exist
                for p in points_str:
                    if p not in points_dict:
                        raise ParserError(
                            f"Point {p} referenced in collinear statement but not declared",
                            1
                        )
                collinear_points = [points_dict[p] for p in points_str]
                initial_facts.append(GeometricFact(type_="Collinear", points=collinear_points))

            elif line.startswith('Parallelogram('):
                points_str = line[14:-1]
                if len(points_str) != 4:
                    raise ParserError(
                        f"Parallelogram requires exactly 4 points, got: {points_str}",
                        1
                    )

                # Validate point ordering
                if not is_valid_parallelogram_ordering(points_str):
                    raise ParserError(
                        f"Invalid parallelogram point order: {points_str}. Must be in cyclic order (e.g. ABCD, BCDA, CDAB, DABC).",
                        2
                    )

                para_points = [points_dict[p] for p in points_str]
                initial_facts.append(GeometricFact(type_="Parallelogram", points=para_points))

            elif line.startswith('Equal(MeasureOfAngle('):
                angle_stmt = parse_angle_statement(line, points_dict)
                if angle_stmt:
                    initial_angles.append(angle_stmt)

        # Also check the CONSTRUCTION_CDL section for collinear points
        construction_cdl = extract_section(content, "CONSTRUCTION_CDL:", "TEXT_CDL:")
        for line in construction_cdl.split('\n'):
            line = line.strip()
            if line.startswith('Collinear('):
                points_str = line[10:-1]
                # Validate points exist
                for p in points_str:
                    if p not in points_dict:
                        raise ParserError(
                            f"Point {p} referenced in collinear statement but not declared",
                            1
                        )
                collinear_points = [points_dict[p] for p in points_str]
                # Check if this collinear fact already exists
                points_set = set(collinear_points)
                if not any(set(fact.points) == points_set for fact in initial_facts if fact.type == "Collinear"):
                    initial_facts.append(GeometricFact(type_="Collinear", points=collinear_points))

        return GeometricState(facts=initial_facts, angles=initial_angles), points_dict

    except ParserError:
        raise
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
        para_points_str = next((arg for arg in theorem.points if len(arg) == 4), None)
        if not para_points_str:
            raise ParserError("Parallelogram theorem requires a 4-point sequence", 1)

        try:
            # Get parallelogram from state
            para_fact = next((f for f in state.facts if f.type == "Parallelogram"), None)
            if not para_fact:
                raise ParserError("No parallelogram found in state", 1)

            # Important: Use the points from the state fact, NOT from the theorem call
            # This ensures we're using the correct order that was established in the state
            points = para_fact.points

            # Use that same order to create angles
            angle1 = makeAngle(points[3], points[0], points[1])  # DAB
            angle2 = makeAngle(points[1], points[2], points[3])  # BCD

            angles = [angle1, angle2]

            print(f"Setting up parallelogram opposite angles:")
            print(f"• ∠{angle1.point1.name}{angle1.vertex.name}{angle1.point2.name} opposite to")
            print(f"• ∠{angle2.point1.name}{angle2.vertex.name}{angle2.point2.name}")

        except KeyError as e:
            missing_point = str(e.args[0])
            raise ParserError(f"Point {missing_point} referenced but not declared", 1)

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

    # First, find the state's parallelogram order if it exists
    state_para = next((f for f in state.facts if f.type == "Parallelogram"), None)
    if state_para:
        state_para_order = ''.join(p.name for p in state_para.points)

    def get_valid_cyclic_rotations(points_str: str) -> List[str]:
        """Get all valid cyclic rotations for a given point string"""
        if len(points_str) != 4:
            return []
        return [points_str[i:] + points_str[:i] for i in range(len(points_str))]

    def check_parallelogram_order(points_str: str) -> Tuple[bool, List[str]]:
        """
        Check if a point string is a valid parallelogram order.
        Returns (is_valid, valid_rotations)
        """
        if len(points_str) != 4:
            return False, []

        # ABCD is valid if:
        # 1. Each point appears exactly once
        # 2. Points are connected in sequence (A-B-C-D-A)
        # Invalid orders like ABDC create diagonal connections
        base = state_para_order
        valid_rotations = get_valid_cyclic_rotations(base)

        # Check if given order is one of the valid rotations
        is_valid = points_str in valid_rotations

        return is_valid, valid_rotations

    for theorem in theorems:
        if theorem.name not in theorem_map:
            return None, GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL,
                message=f"Unknown theorem: {theorem.name}"
            )

        if theorem.name == 'parallelogram_property_opposite_angle_equal':
            para_points_str = next((arg for arg in theorem.points if len(arg) == 4), None)
            if para_points_str:
                # Check if order is valid before anything else
                is_valid, valid_rotations = check_parallelogram_order(para_points_str)
                if not is_valid:
                    return None, GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Invalid parallelogram order: {para_points_str}",
                        details=f"Points must follow the edges of the parallelogram in sequence. "
                                f"For parallelogram {state_para_order}, valid orders are: {valid_rotations}"
                    )

                # Then get and validate the premise
                premise = theorem.premise
                if premise and 'Parallelogram(' in premise:
                    premise_para = premise[premise.find('Parallelogram(') + 14:].split(')')[0]

                    # Premise must match state's parallelogram order
                    if premise_para != state_para_order:
                        return None, GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Premise order ({premise_para}) must match state's parallelogram order ({state_para_order})",
                            details=f"The premise must use the exact same order as defined in the state"
                        )

        # Rest of the theorems remain unchanged...
        elif theorem.name == 'adjacent_complementary_angle':
            # Get collinear points from premise
            premise = theorem.premise
            if premise and 'Collinear(' in premise:
                collinear_str = premise[premise.find('Collinear(') + 10:premise.find(')')]
                collinear_points = [points_dict[p] for p in collinear_str]

                # Check if these points are actually collinear in the state
                found_collinear = False
                for fact in state.facts:
                    if fact.type == "Collinear":
                        if set(collinear_points).issubset(set(fact.points)):
                            found_collinear = True
                            break

                if not found_collinear:
                    return None, GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Points {[p.name for p in collinear_points]} not proven collinear",
                        details="The premise requires these points to be collinear, but this hasn't been established in the state"
                    )

        elif theorem.name == 'angle_addition':
            if len(theorem.points) >= 2:
                angle_points = [pt for pt in theorem.points if len(pt) == 3]
                if len(angle_points) >= 2:
                    angle1_points = angle_points[0]
                    angle2_points = angle_points[1]

                    # Check that angles share vertex
                    if angle1_points[1] != angle2_points[1]:
                        return None, GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Angles {angle1_points} and {angle2_points} do not share a vertex",
                            details="The angle addition theorem requires angles to share a vertex"
                        )

                    # Check that angles share exactly one ray
                    rays1 = {angle1_points[0], angle1_points[2]}
                    rays2 = {angle2_points[0], angle2_points[2]}
                    shared_rays = rays1.intersection(rays2)

                    if len(shared_rays) != 1:
                        return None, GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Angles {angle1_points} and {angle2_points} must share exactly one ray",
                            details="The angle addition theorem requires angles to share exactly one ray"
                        )

        try:
            # Apply theorem
            rule = theorem_map[theorem.name]
            points, lines, angles = setup_theorem_points_and_angles(theorem, points_dict, current_state)

            print("\nApplying theorem:", theorem.name)
            print("Points:", [p.name for p in points])
            print("Angles:", [f"∠{a.point1.name}{a.vertex.name}{a.point2.name}" for a in angles])

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

        try:
            # Create initial state (this may raise ParserError with tier info)
            initial_state, points_dict = create_initial_state(content)
        except ParserError as e:
            if e.tier == 2:  # Premise violation
                print(f"\nError in Tier {e.tier}: TIER2_PREMISE")
                print("=" * 40)
                print(f"Message: {e.message}")
                return False
            else:  # Default to tier 1 for theorem/parsing errors
                print(f"\nError in Tier {e.tier}: TIER1_THEOREM_CALL")
                print("=" * 40)
                print(f"Message: {e.message}")
                return False

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
        try:
            theorems = parse_theorem_sequence(theorem_sequence)
        except ParserError as e:
            print(f"\nError in Tier {e.tier}: TIER1_THEOREM_CALL")
            print("=" * 40)
            print(f"Message: {e.message}")
            return False

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
        if e.tier == 2:
            print(f"\nError in Tier 2: TIER2_PREMISE")
        else:
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
    result = verify_geometric_proof("/questions/question2/question2_2")
    print(f"Verification {'succeeded' if result else 'failed'}")


