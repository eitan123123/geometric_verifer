from z3 import *
import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple
from enum import Enum
from typing import Tuple, Optional




class ErrorTier(Enum):
    TIER1_THEOREM_CALL = 1    # Incorrect theorem call
    TIER2_PREMISE = 2         # Premise violation
    TIER3_GOAL_NOT_REACHED = 3  # Failed to reach goal

@dataclass
class GeometricError:
    tier: ErrorTier
    message: str
    details: Optional[str] = None

@dataclass
class GeometricPoint:
    name: str


@dataclass
class GeometricAngle:
    point1: GeometricPoint
    vertex: GeometricPoint
    point2: GeometricPoint


class GeometricTheorem:
    def __init__(self):
        self.solver = Solver()
        self.points: Dict[str, GeometricPoint] = {}
        self.angles: Dict[str, Real] = {}
        self.parallel_pairs: Set[Tuple[str, str]] = set()
        self.perpendicular_pairs: Set[Tuple[str, str]] = set()
        self.collinear_facts: List[List[str]] = []
        self.algebraic_angles: Dict[str, str] = {}
        self.a = Real('a')  # Create variable for algebraic expressions

    def add_point(self, name: str) -> GeometricPoint:
        if name not in self.points:
            self.points[name] = GeometricPoint(name)
        return self.points[name]

    def add_angle(self, p1: str, v: str, p2: str) -> Real:
        """Add an angle variable to Z3 solver"""
        # Normalize the angle name
        normalized = self.normalize_angle_name(p1 + v + p2)
        angle_name = f"angle_{normalized}"

        if angle_name not in self.angles:
            self.angles[angle_name] = Real(angle_name)
            # Add basic angle constraints (0 <= angle <= 180)
            self.solver.add(self.angles[angle_name] >= 0)
            self.solver.add(self.angles[angle_name] <= 180)
        return self.angles[angle_name]

    def normalize_angle_name(self, angle_points: str) -> str:
        """Normalize angle name (ABC and CBA are the same angle)"""
        p1, v, p2 = angle_points[0], angle_points[1], angle_points[2]
        # Return the lexicographically smaller version
        if p1 > p2:
            return f"{p2}{v}{p1}"
        return f"{p1}{v}{p2}"

    def add_collinear_fact(self, points: List[str]):
        """Add collinear points fact with supplementary angle relationships"""
        if len(points) < 3:
            return

        # For each three consecutive points
        for i in range(len(points) - 2):
            p1, v, p2 = points[i:i + 3]

            # Add points if they don't exist
            for p in [p1, v, p2]:
                if p not in self.points:
                    self.add_point(p)

            # Add straight angle constraint (180°)
            angle = self.add_angle(p1, v, p2)
            rev_angle = self.add_angle(p2, v, p1)

            # These points form a straight line (180°)
            self.solver.add(angle == 180)
            self.solver.add(rev_angle == 180)

            # Any other point forms supplementary angles with this line
            for q in self.points:
                if q not in [p1, v, p2]:
                    # Add the supplementary angles
                    q_angle1 = self.add_angle(p1, v, q)
                    q_angle2 = self.add_angle(q, v, p2)

                    # These angles must be supplementary
                    self.solver.add(q_angle1 + q_angle2 == 180)

                    # Each angle must be between 0° and 180°
                    self.solver.add(q_angle1 > 0)
                    self.solver.add(q_angle1 < 180)
                    self.solver.add(q_angle2 > 0)
                    self.solver.add(q_angle2 < 180)

                    # If one angle is known, the other must be its supplement
                    if q_angle1 in self.solver.assertions():
                        for assertion in self.solver.assertions():
                            if str(assertion).startswith(str(q_angle1)):
                                try:
                                    val = float(str(assertion).split(" == ")[1])
                                    self.solver.add(q_angle2 == 180 - val)
                                except:
                                    continue

    def parse_algebraic_expression(self, expr: str, var):
        """Convert string expression to Z3 expression generically"""
        expr = expr.strip()
        try:
            if isinstance(expr, (int, float)):
                return float(expr)

            # Handle pure variable case
            if expr == 'a':
                return var

            # Handle basic arithmetic expressions
            if '+' in expr:
                left, right = expr.rsplit('+', 1)
                return self.parse_algebraic_expression(left, var) + self.parse_algebraic_expression(right, var)
            elif '-' in expr and not expr.startswith('-'):
                left, right = expr.rsplit('-', 1)
                return self.parse_algebraic_expression(left, var) - self.parse_algebraic_expression(right, var)
            elif expr.startswith('-'):
                return -self.parse_algebraic_expression(expr[1:], var)
            elif '/' in expr:
                num, denom = expr.split('/')
                return self.parse_algebraic_expression(num, var) / self.parse_algebraic_expression(denom, var)
            elif '*' in expr:
                left, right = expr.split('*')
                return self.parse_algebraic_expression(left, var) * self.parse_algebraic_expression(right, var)

            # Try to convert to float if it's a number
            try:
                return float(expr)
            except ValueError:
                return var  # Default to variable if nothing else matches

        except Exception as e:
            print(f"Error parsing expression '{expr}': {str(e)}")
            return var

    def add_algebraic_angle(self, angle_name: str, expression: str):
        """Add an angle with an algebraic expression"""
        print(f"Adding algebraic angle constraint: {angle_name} = {expression}")
        angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])
        expr = self.parse_algebraic_expression(expression, self.a)
        self.solver.add(angle_var == expr)




    def add_parallel_lines(self, line1: str, line2: str):
        """Add parallel lines constraint"""
        if len(line1) != 2 or len(line2) != 2:
            raise ValueError("Each line must be specified by exactly 2 points")

        # Add the parallel pair
        pair = tuple(sorted([line1, line2]))
        self.parallel_pairs.add(pair)

        # For parallel lines:
        # 1. Corresponding angles must be equal
        angle1 = self.add_angle(line1[0], line1[1], line2[1])
        angle2 = self.add_angle(line2[0], line2[1], line1[1])
        self.solver.add(angle1 == angle2)

        # 2. Alternate interior angles must be equal
        alt_angle1 = self.add_angle(line2[0], line1[1], line1[0])
        alt_angle2 = self.add_angle(line1[0], line2[1], line2[0])
        self.solver.add(alt_angle1 == alt_angle2)

        # 3. Sum of adjacent angles must be 180°
        self.solver.add(angle1 + alt_angle1 == 180)
        self.solver.add(angle2 + alt_angle2 == 180)

    def add_perpendicular_lines(self, line1: str, line2: str):
        """Add perpendicular lines constraint"""
        if len(line1) != 2 or len(line2) != 2:
            raise ValueError("Each line must be specified by exactly 2 points")

        # Add the perpendicular pair
        pair = tuple(sorted([line1, line2]))
        self.perpendicular_pairs.add(pair)

        # For perpendicular lines, the angle between them must be 90 degrees
        angle = self.add_angle(line1[0], line1[1], line2[1])
        self.solver.add(angle == 90)

    def add_parallelogram(self, points: str):
        """Add parallelogram fact with its constraints"""
        if len(points) != 4:
            raise ValueError("Parallelogram must have exactly 4 points")

        # Get points in order ABCD
        A = points[0]
        B = points[1]
        C = points[2]
        D = points[3]

        # Add interior angles
        angle_DAB = self.add_angle(D, A, B)
        angle_ABC = self.add_angle(A, B, C)
        angle_BCD = self.add_angle(B, C, D)
        angle_CDA = self.add_angle(C, D, A)

        # Basic angle constraints
        for angle in [angle_DAB, angle_ABC, angle_BCD, angle_CDA]:
            self.solver.add(angle > 0)
            self.solver.add(angle < 180)

        # Parallelogram properties:
        # 1. Opposite angles are equal
        self.solver.add(angle_DAB == angle_BCD)
        self.solver.add(angle_ABC == angle_CDA)

        # 2. Adjacent angles are supplementary
        self.solver.add(angle_DAB + angle_ABC == 180)
        self.solver.add(angle_ABC + angle_BCD == 180)
        self.solver.add(angle_BCD + angle_CDA == 180)
        self.solver.add(angle_CDA + angle_DAB == 180)

        # 3. Sum of angles is 360°
        self.solver.add(angle_DAB + angle_ABC + angle_BCD + angle_CDA == 360)

        # Add parallel sides
        self.add_parallel_lines(A + B, C + D)  # AB || CD
        self.add_parallel_lines(B + C, D + A)  # BC || DA

    def verify_goal_angle(self, p1: str, v: str, p2: str, expected: float, epsilon: float = 1e-10) -> bool:
        print(f"\nVerifying goal angle: {p1}{v}{p2}")

        # Get or create the goal angle
        angle = self.add_angle(p1, v, p2)

        # Print current state for debugging
        print("\nCurrent constraints:")
        for constraint in self.solver.assertions():
            print(constraint)

        # Check if system is satisfiable
        check_result = self.solver.check()
        if check_result != sat:
            print("Error: System is unsatisfiable")
            return False

        model = self.solver.model()
        print("\nFull model:", model)

        # Try to find our angle in the model
        try:
            for decl in model.decls():
                if str(decl) == str(angle.decl()):
                    val = model[decl]
                    if val is not None:
                        # Convert the value to a float
                        if hasattr(val, 'as_decimal'):
                            angle_val = float(val.as_decimal(10).rstrip('?'))
                        else:
                            num = float(val.numerator_as_long())
                            den = float(val.denominator_as_long())
                            angle_val = num / den

                        print(f"\nVerification Result:")
                        print(f"Expected value: {expected}°")
                        print(f"Calculated value: {angle_val}°")

                        return abs(angle_val - expected) < epsilon

            print("Error: Could not find angle in model")
            return False

        except Exception as e:
            print(f"Error during verification: {str(e)}")
            return False

    def add_angle_measure(self, p1: str, v: str, p2: str, measure: float):
        """Add known angle measure"""
        # First add the angle and its reverse
        angle = self.add_angle(p1, v, p2)
        rev_angle = self.add_angle(p2, v, p1)

        # Set the measure
        self.solver.add(angle == measure)
        self.solver.add(rev_angle == measure)

        # For all other points, maintain angle relationships
        for point in self.points:
            if point not in [p1, v, p2]:
                # Create the other angle
                other_angle = self.add_angle(p1, v, point)

                # If these points are collinear, they form 180°
                # Check if there's a collinear fact containing these points
                for fact in self.solver.assertions():
                    if str(fact).startswith("angle_") and str(fact).endswith(" == 180"):
                        points_involved = set([p1, v, p2, point])
                        if all(p in str(fact) for p in points_involved):
                            self.solver.add(other_angle + measure == 180)

                # Add basic angle constraints
                self.solver.add(other_angle >= 0)
                self.solver.add(other_angle <= 180)

    def verify_goal_angle(self, p1: str, v: str, p2: str, expected: float, epsilon: float = 1e-10) -> bool:
        """Verify if an angle measure matches the expected value"""
        print("\nStarting verification for angle:", p1 + v + p2)

        # Get or create the goal angle
        angle = self.add_angle(p1, v, p2)

        # Check if satisfiable
        check_result = self.solver.check()
        if check_result != sat:
            print("Error: System is unsatisfiable")
            return False

        # Get and print the model
        model = self.solver.model()
        print("\nFull model:", model)  # Debug print

        try:
            # Try to find the angle value
            for decl in model.decls():
                if str(decl) == str(angle.decl()):
                    val = model[decl]
                    if val is not None:
                        try:
                            if hasattr(val, 'as_decimal'):
                                angle_val = float(val.as_decimal(10).rstrip('?'))
                            else:
                                num = float(val.numerator_as_long())
                                den = float(val.denominator_as_long())
                                angle_val = num / den

                            print(f"\nVerification Result:")
                            print(f"Expected value: {expected}°")
                            print(f"Calculated value: {angle_val}°")

                            if abs(angle_val - expected) < epsilon:
                                print("Verification: ✓ Successful")
                                return True
                            else:
                                print("Verification: ✗ Failed - Values don't match")
                                return False
                        except Exception as e:
                            print(f"Error converting value: {str(e)}")
                            return False

            print("\nError: Could not find angle in model")
            return False

        except Exception as e:
            print(f"Error during verification: {str(e)}")
            return False

    def print_current_state(self):
        """Print the current state of the geometric system"""
        print("\nCurrent Geometric State:")
        print("=======================")
        print("\nPoints:", list(self.points.keys()))
        print("\nAngle Variables:", list(self.angles.keys()))
        print("\nParallel Pairs:", self.parallel_pairs)
        print("\nSolver Constraints:")
        for c in self.solver.assertions():
            print(c)
    def debug_state(self):
        """Print current state of the geometric system"""
        print("\nDebug State:")
        print("===========")
        print("Points:", list(self.points.keys()))
        print("\nAngles:")
        check_result = self.solver.check()
        if check_result == sat:
            model = self.solver.model()
            for angle_name, angle_var in self.angles.items():
                if angle_var in model:
                    val = model[angle_var]
                    try:
                        angle_val = float(val.as_decimal(10).rstrip('?'))
                    except:
                        angle_val = float(val.numerator_as_long()) / float(val.denominator_as_long())
                    print(f"{angle_name}: {angle_val}°")
        print("\nParallel pairs:", self.parallel_pairs)
        print("\nConstraints:")
        print(self.solver)

    def add_complementary_angle_fact(self, p1: str, v: str, p2: str, angle_measure: float):
        """Add a fact about complementary angles"""
        # Add primary angle
        angle = self.add_angle(p1, v, p2)
        self.solver.add(angle == angle_measure)

        # Add constraint for complementary angles
        for other_p in self.points:
            if other_p not in [p1, v, p2]:
                other_angle = self.add_angle(p1, v, other_p)
                shared_angle = self.add_angle(p2, v, other_p)
                # If angles share a ray, they must sum to the original angle
                self.solver.add(Or(
                    other_angle + shared_angle == angle,
                    other_angle + shared_angle == 180 - angle
                ))

    def add_collinear_angle_relationship(self, angle1_points: tuple, angle2_points: tuple):
        """Add relationship between angles that share a vertex in a collinear configuration"""
        if angle1_points[1] != angle2_points[1]:  # Must share vertex
            return

        v = angle1_points[1]  # Shared vertex

        # Create both angles
        angle1 = self.add_angle(angle1_points[0], v, angle1_points[2])
        angle2 = self.add_angle(angle2_points[0], v, angle2_points[2])

        # Add supplementary angle relationship
        self.solver.add(angle1 + angle2 == 180)

    def validate_theorem_premises(self, theorem_name: str, args: List[str], premise: str) -> Tuple[
        bool, Optional[GeometricError]]:
        """Validate theorem premises and return appropriate error if validation fails"""

        if theorem_name == "adjacent_complementary_angle":
            # Check for collinear points in premise
            if "Collinear" in premise:
                collinear_match = re.search(r'Collinear\((\w+)\)', premise)
                if collinear_match:
                    points = collinear_match.group(1)
                    # Check if these points exist in collinear_facts
                    point_set = set(points)
                    collinear_found = False
                    for fact in self.collinear_facts:
                        if point_set.issubset(set(fact)):
                            collinear_found = True
                            break

                    if not collinear_found:
                        return False, GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Points {points} are not proven collinear",
                            details=f"Known collinear facts: {self.collinear_facts}"
                        )

                    # Also verify the angles exist
                    if len(args) < 3:
                        return False, GeometricError(
                            tier=ErrorTier.TIER1_THEOREM_CALL,
                            message="Missing angle arguments",
                            details="adjacent_complementary_angle requires two angles"
                        )

                    # Verify angle points share a vertex and are on the collinear line
                    angle1_points = args[1]
                    angle2_points = args[2]
                    if not (angle1_points[1] == angle2_points[1] and
                            all(p in points for p in [angle1_points[1], angle2_points[1]])):
                        return False, GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Angles {angle1_points} and {angle2_points} must share a vertex on collinear line {points}"
                        )
                else:
                    return False, GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Invalid collinear points format in premise"
                    )
            else:
                return False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing collinear points in premise",
                    details="adjacent_complementary_angle theorem requires collinear points"
                )


        elif theorem_name == "parallelogram_property_opposite_angle_equal":

            if len(args) < 2:
                return False, GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Missing parallelogram argument",

                    details="parallelogram_property_opposite_angle_equal requires a parallelogram name"

                )

            theorem_para = args[1]

            # Extract the parallelogram from the premise

            premise_match = re.search(r'Parallelogram\((\w+)\)', premise)

            if not premise_match:
                return False, GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Invalid parallelogram format in premise"

                )

            premise_para = premise_match.group(1)

            # Check if premise parallelogram exists in our stored parallelograms

            if not any(cyclic_var == premise_para for cyclic_var in self.parallelograms):
                return False, GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Parallelogram {premise_para} is not defined in TEXT_CDL",

                    details=f"Available parallelograms: {', '.join(self.parallelograms)}"

                )

            # Check if the theorem argument matches the premise parallelogram

            if theorem_para != premise_para:
                return False, GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Theorem uses parallelogram {theorem_para} but premise specifies {premise_para}",

                    details="Theorem argument must match the parallelogram in the premise"

                )

        elif theorem_name == "parallel_property_alternate_interior_angle":
            if "ParallelBetweenLine" not in premise:
                return False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing parallel lines in premise",
                    details="parallel_property_alternate_interior_angle theorem requires parallel lines"
                )

            line_match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', premise)
            if not line_match:
                return False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Invalid parallel lines format in premise"
                )

            line1, line2 = line_match.group(1), line_match.group(2)
            if (line1, line2) not in self.parallel_pairs and (line2, line1) not in self.parallel_pairs:
                return False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Lines {line1} and {line2} not proven parallel",
                    details=f"Available parallel pairs: {self.parallel_pairs}"
                )

            # Verify there's a transversal line
            if len(args) < 3:
                return False, GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing line arguments",
                    details="parallel_property_alternate_interior_angle requires two parallel lines"
                )

        elif theorem_name == "angle_addition":
            # Verify angles share a vertex
            if len(args) < 3:
                return False, GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing angle arguments",
                    details="angle_addition requires at least two angles"
                )

            angle1 = args[1] if len(args) > 1 else ""
            angle2 = args[2] if len(args) > 2 else ""

            if len(angle1) != 3 or len(angle2) != 3:
                return False, GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid angle format",
                    details="Each angle must be specified by exactly 3 points"
                )

            if angle1[1] != angle2[1]:
                return False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Angles {angle1} and {angle2} must share a vertex",
                    details="Required for angle addition"
                )


        elif theorem_name == "quadrilateral_property_angle_sum":
            if len(args) < 2:
                return False, GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid number of arguments",
                    details="Expected quadrilateral name for angle sum theorem"
                )

            quad_name = args[1]
            if f"Polygon({quad_name})" not in premise:
                return False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Quadrilateral {quad_name} is not defined in premise",
                    details="Quadrilateral must be defined as a polygon"
                )

            return True, None

        return True, None

    def check_collinearity(self, points: str) -> bool:
        """Check if points are collinear in our stored facts"""
        point_set = set(points)
        for fact in self.collinear_facts:
            if point_set.issubset(set(fact)):
                return True
        return False

    def parse_and_verify_proof(self, content: str) -> bool:
        try:
            self.parallelograms = set()
            self.collinear_facts = []
            self.parallel_pairs = set()
            sections = {}
            current_section = None

            # Parse sections (keep existing section parsing code)
            print("\nParsing sections...")
            for line in content.split('\n'):
                line = line.strip()
                if not line:
                    continue

                # Modified section detection
                if (line.endswith('CDL:') or
                        line.endswith('CDL_EXTENDED:') or  # Added this line
                        line.endswith('SEQUENCE:') or
                        line == 'ANSWER:'):
                    current_section = line[:-1] if line.endswith(':') else line
                    sections[current_section] = []
                    print(f"Found section: {current_section}")
                elif current_section:
                    sections[current_section].append(line)

            print("\nAvailable sections:", list(sections.keys()))

            # Process CONSTRUCTION_CDL_EXTENDED first
            if 'CONSTRUCTION_CDL_EXTENDED' in sections:
                print("\nProcessing CONSTRUCTION_CDL_EXTENDED section...")
                for line in sections['CONSTRUCTION_CDL_EXTENDED']:
                    print(f"Processing line: {line}")
                    if line.startswith('ParallelBetweenLine('):
                        match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', line)
                        if match:
                            line1, line2 = match.group(1), match.group(2)
                            print(f"Found parallel lines: {line1} || {line2}")
                            pair = tuple(sorted([line1, line2]))
                            self.parallel_pairs.add(pair)
                            # Add reversed pair too
                            self.parallel_pairs.add(tuple([line2, line1]))
                            print(f"Added parallel pairs: {pair} and {(line2, line1)}")
                    if line.startswith('Shape('):
                        continue
                        # Skip SYMBOLS_AND_VALUES, EQUATIONS
                    if line.startswith('SYMBOLS_AND_VALUES:') or line.startswith('EQUATIONS:'):
                        continue

                    if line.startswith('Point('):
                        name = line[6:-1]
                        self.add_point(name)
                    elif line.startswith('ParallelBetweenLine('):
                        match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', line)
                        if match:
                            line1, line2 = match.group(1), match.group(2)
                            print(f"Found parallel lines: {line1} || {line2}")
                            pair = tuple(sorted([line1, line2]))
                            self.parallel_pairs.add(pair)
                            # Add reversed pair too
                            self.parallel_pairs.add(tuple([line2, line1]))
                            print(f"Added parallel pairs: {pair} and {(line2, line1)}")

            # Parse goal and verify


            # Process CONSTRUCTION_CDL facts
            if 'CONSTRUCTION_CDL' in sections:
                for line in sections['CONSTRUCTION_CDL']:
                    if line.startswith('Collinear('):
                        points = line[10:-1]
                        self.collinear_facts.append(list(points))
                        self.add_collinear_fact(list(points))

            # Parse TEXT_CDL facts
            # Inside parse_and_verify_proof method
            # Inside parse_and_verify_proof method
            if 'TEXT_CDL' in sections:
                for line in sections['TEXT_CDL']:
                    if line.startswith('Equal(MeasureOfAngle('):
                        match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                        if match:
                            angle_points = match.group(1)  # e.g., 'ECD' or 'DCE'
                            expression = match.group(2)  # e.g., '70' or 'a+2'
                            print(f"Adding algebraic angle: {angle_points} = {expression}")

                            # Normalize the angle points
                            normalized_angle = self.normalize_angle_name(angle_points)

                            # Add points if they don't exist
                            for p in normalized_angle:
                                if p not in self.points:
                                    self.add_point(p)

                            # Add the angle with its algebraic expression
                            if expression.isdigit():  # Handle concrete values
                                self.add_angle_measure(normalized_angle[0], normalized_angle[1], normalized_angle[2],
                                                       float(expression))
                            else:  # Handle algebraic expressions
                                self.add_algebraic_angle(normalized_angle, expression)
                    elif line.startswith('Parallelogram('):
                        # Extract parallelogram name
                        para_match = re.match(r'Parallelogram\((\w+)\)', line)
                        if para_match:
                            para_name = para_match.group(1)
                            print(f"Found parallelogram: {para_name}")
                            self.parallelograms.update(get_cyclic_variations(para_name))  # Add cyclic variations
                            print(f"Updated parallelograms set: {self.parallelograms}")
            print("\nCollected facts:")
            print("Collinear points:", self.collinear_facts)
            print("Parallel pairs:", self.parallel_pairs)
            print("Points:", list(self.points.keys()))

            # Process theorem sequence
            # Inside parse_and_verify_proof method
            # Process theorem sequence before verifying goal
            if 'THEOREM_SEQUENCE' in sections:
                sequence_text = '\n'.join(sections['THEOREM_SEQUENCE'])
                # Handle both formats of step specification
                if 'Step' in sequence_text:
                    steps = [step.strip() for step in sequence_text.split('Step') if step.strip()]
                else:
                    # Handle step_id format
                    steps = [step.strip() for step in sequence_text.split('step_id:') if step.strip()]

                for step in steps:
                    # Handle both formats
                    if 'Theorem:' in step:
                        # Format: "Step 1: Theorem: ..."
                        theorem_match = re.search(r'Theorem:\s*(\w+)\((.*?)\)', step)
                        premise_match = re.search(r'Premise:\s*(.*?)\s*Conclusion:', step, re.DOTALL)
                    else:
                        # Format: "1; theorem: ..."
                        theorem_match = re.search(r'theorem:\s*(\w+)\((.*?)\)', step)
                        premise_match = re.search(r'premise:\s*(.*?);\s*conclusion:', step)

                    conclusion_match = re.search(r'[Cc]onclusion:\s*(\[.*?\])', step)

                    if theorem_match:
                        theorem_name = theorem_match.group(1)
                        args = [arg.strip() for arg in theorem_match.group(2).split(',')]
                        premise = premise_match.group(1).strip() if premise_match else ""
                        conclusions = eval(conclusion_match.group(1)) if conclusion_match else []

                        print(f"\nProcessing theorem: {theorem_name}")
                        print(f"Arguments: {args}")
                        print(f"Premise: '{premise}'")
                        print(f"Conclusions: {conclusions}")

                        # Validate premises first
                        is_valid, error = self.validate_theorem_premises(theorem_name, args, premise)
                        if not is_valid:
                            print(f"\nError in {error.tier.name}:")
                            print(f"Message: {error.message}")
                            if error.details:
                                print(f"Details: {error.details}")
                            return False

                        # Then process theorem step
                        error = self.process_theorem_step(theorem_name, args, premise, conclusions)
                        if error:
                            print(f"\nError in {error.tier.name}:")
                            print(f"Message: {error.message}")
                            if error.details:
                                print(f"Details: {error.details}")
                            return False

            if 'GOAL_CDL' in sections:
                goal_line = sections['GOAL_CDL'][0]
                goal_match = re.search(r'Value\(MeasureOfAngle\((\w+)\)\)', goal_line)
                if not goal_match:
                    print("Error: Could not parse goal angle")
                    return False
                goal_angle = goal_match.group(1)

                if 'ANSWER' in sections and sections['ANSWER']:
                    expected_answer = float(sections['ANSWER'][0])
                    print(f"\nGoal angle: {goal_angle}")
                    print(f"Expected answer: {expected_answer}")

                    if self.algebraic_angles:  # If we have algebraic angles, use algebraic verification
                        return self.verify_algebraic_goal(goal_angle, expected_answer)
                    else:  # Otherwise use regular verification
                        return self.verify_goal_angle(goal_angle[0], goal_angle[1], goal_angle[2], expected_answer)

            return True

        except Exception as e:

            print(f"Error during proof verification: {str(e)}")

            import traceback

            traceback.print_exc()

            return False

    def verify_algebraic_goal(self, goal_angle: str, expected: float, epsilon: float = 1e-10) -> bool:
        print(f"\nVerifying algebraic goal angle: {goal_angle}")

        print("\nCurrent constraints:")
        for constraint in self.solver.assertions():
            print(constraint)

        check_result = self.solver.check()
        if check_result != sat:
            print("Error: System is unsatisfiable")
            return False

        model = self.solver.model()
        print("\nModel:", model)

        # Get all angles
        angles = {}
        for decl in model.decls():
            if str(decl).startswith('angle_'):
                val = model[decl]
                if val is not None:
                    try:
                        if val.is_real():
                            num = float(val.numerator_as_long())
                            den = float(val.denominator_as_long())
                            angles[str(decl)] = num / den
                    except Exception:
                        continue

        print("\nAll angles in model:", angles)

        # Find goal angle
        angle_var = self.add_angle(goal_angle[0], goal_angle[1], goal_angle[2])
        angle_name = str(angle_var.decl())
        if angle_name in angles:
            print(f"\nExpected: {expected}°")
            print(f"Calculated: {angles[angle_name]}°")
            return abs(angles[angle_name] - expected) < epsilon

        print("Error: Could not find goal angle in model")
        return False
    def process_theorem_step(self, theorem_name: str, args: List[str], premise: str, conclusions: List[str]) -> \
    Optional[GeometricError]:
        print(f"\nProcessing theorem step: {theorem_name}")
        print(f"Arguments: {args}")
        print(f"Premise: '{premise}'")
        print(f"Conclusions: {conclusions}")

        # Move the theorem validation up here
        valid_theorems = [
            "parallelogram_property_opposite_angle_equal",
            "adjacent_complementary_angle",
            "parallel_property_alternate_interior_angle",
            "angle_addition",
            "quadrilateral_property_angle_sum"
        ]
        if theorem_name not in valid_theorems:
            return GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL,
                message=f"Unknown theorem: {theorem_name}",
                details=f"Valid theorems are: {valid_theorems}"
            )

        if theorem_name == "quadrilateral_property_angle_sum":
            if len(args) < 2:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid number of arguments",
                    details="Expected quadrilateral name"
                )

            quad_name = args[1]  # e.g., "XWZY"
            angles = []

            # Get angles in correct order around the quadrilateral
            for i in range(len(quad_name)):
                p1 = quad_name[i]
                p2 = quad_name[(i + 1) % len(quad_name)]
                p3 = quad_name[(i + 2) % len(quad_name)]
                angle = self.add_angle(p1, p2, p3)
                angles.append(angle)
                print(f"Added angle {p1}{p2}{p3}")

            # Add quadrilateral angle sum constraint
            self.solver.add(sum(angles) == 360)
            print(f"Added quadrilateral sum constraint: {angles[0]} + {angles[1]} + {angles[2]} + {angles[3]} = 360")


        elif theorem_name == "parallelogram_property_opposite_angle_equal":

            if len(args) < 2:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Missing parallelogram argument",

                    details="Expected parallelogram name"

                )

            # Get angles from conclusion

            angles_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),\s*MeasureOfAngle\((\w+)\)\)', conclusions[0])

            if angles_match:
                angle1, angle2 = angles_match.group(1), angles_match.group(2)

                angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])

                angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                self.solver.add(angle1_var == angle2_var)

                print(f"Added parallelogram opposite angle equality: {angle1} = {angle2}")


        elif theorem_name == "adjacent_complementary_angle":
            if len(args) < 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing angle arguments",
                    details="Expected two angles"
                )

            angle1_points = args[1]
            angle2_points = args[2]

            angle1_var = self.add_angle(angle1_points[0], angle1_points[1], angle1_points[2])
            angle2_var = self.add_angle(angle2_points[0], angle2_points[1], angle2_points[2])

            # Add supplementary angle relationship
            self.solver.add(angle1_var + angle2_var == 180)
            print(f"Added supplementary angle constraint: {angle1_points} + {angle2_points} = 180")

        return None






def get_cyclic_variations(para_name: str) -> Set[str]:
    """Get all cyclic variations of a parallelogram name
    For example, ABCD generates: ABCD, BCDA, CDAB, DABC
    But not reversed versions like DCBA
    """
    variations = set()
    n = len(para_name)
    for i in range(n):
        variations.add(para_name[i:] + para_name[:i])
    return variations


def verify_geometric_proof(filename: str) -> bool:
    """Main function to verify a geometric proof"""
    try:
        with open(filename, 'r') as file:
            content = file.read()

        theorem = GeometricTheorem()
        result = theorem.parse_and_verify_proof(content)
        print(f"\nOverall verification {'succeeded' if result else 'failed'}")
        return result
    except Exception as e:
        print(f"Error: {str(e)}")
        return False


if __name__ == "__main__":
    theorem = GeometricTheorem()
    result = verify_geometric_proof("/questions/the new format for questions after jan_17/question2/question2_13")
    theorem.debug_state()  # Add this line
    print(f"Verification {'succeeded' if result else 'failed'}")