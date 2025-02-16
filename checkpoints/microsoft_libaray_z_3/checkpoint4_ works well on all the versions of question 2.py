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
        self.collinear_facts: List[List[str]] = []  # Add this line

    def add_point(self, name: str) -> GeometricPoint:
        if name not in self.points:
            self.points[name] = GeometricPoint(name)
        return self.points[name]

    def add_angle(self, p1: str, v: str, p2: str) -> Real:
        """Add an angle variable to Z3 solver"""
        angle_name = f"angle_{p1}{v}{p2}"
        if angle_name not in self.angles:
            self.angles[angle_name] = Real(angle_name)
            # Add basic angle constraints (0 <= angle <= 180)
            self.solver.add(self.angles[angle_name] >= 0)
            self.solver.add(self.angles[angle_name] <= 180)
        return self.angles[angle_name]

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
        """Verify if an angle measure matches the expected value"""
        print("\nStarting verification for angle:", p1 + v + p2)

        # Get the goal angle and its reverse
        angle = self.add_angle(p1, v, p2)
        rev_angle = self.add_angle(p2, v, p1)

        # First check without adding additional constraints
        check_result = self.solver.check()
        if check_result != sat:
            print("Error: System is unsatisfiable")
            return False

        # Save the current set of constraints
        self.solver.push()

        # Add strict equality constraint for the expected value
        self.solver.add(angle == expected)
        self.solver.add(rev_angle == expected)

        # Check with the new constraint
        check_result = self.solver.check()
        if check_result != sat:
            print("Error: System is unsatisfiable with expected value")
            self.solver.pop()
            return False

        # Get the model
        model = self.solver.model()
        print("\nFull model:", model)

        # Find our angle in the model
        if angle.decl() in model:
            val = model[angle.decl()]
            try:
                if val.is_real():
                    num = float(val.numerator_as_long())
                    den = float(val.denominator_as_long())
                    angle_val = num / den if den != 0 else float(val.as_decimal(10).rstrip('?'))

                    print(f"\nVerification Result:")
                    print(f"Expected value: {expected}°")
                    print(f"Calculated value: {angle_val}°")

                    result = abs(angle_val - expected) < epsilon
                    print(f"Verification: {'✓ Successful' if result else '✗ Failed - Values dont match'}")

                    self.solver.pop()
                    return result

            except Exception as e:
                print(f"Error converting value: {str(e)}")
                self.solver.pop()
                return False

        self.solver.pop()
        print("\nError: Could not find angle in model")
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

            # Parse sections
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

            # Process CONSTRUCTION_CDL facts
            if 'CONSTRUCTION_CDL' in sections:
                for line in sections['CONSTRUCTION_CDL']:
                    if line.startswith('Collinear('):
                        points = line[10:-1]
                        self.collinear_facts.append(list(points))
                        self.add_collinear_fact(list(points))

            # Parse TEXT_CDL facts
            if 'TEXT_CDL' in sections:
                for line in sections['TEXT_CDL']:
                    if line.startswith('Collinear('):
                        points = line[10:-1]
                        if list(points) not in self.collinear_facts:
                            self.collinear_facts.append(list(points))
                            self.add_collinear_fact(list(points))
                    elif line.startswith('Equal(MeasureOfAngle('):
                        match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),(\d+)\)', line)
                        if match:
                            angle_points = match.group(1)
                            measure = float(match.group(2))
                            self.add_angle_measure(angle_points[0], angle_points[1], angle_points[2], measure)
                    elif line.startswith('Parallelogram('):
                        para_name = line[14:-1].strip()
                        # Add all cyclic variations
                        self.parallelograms.update(get_cyclic_variations(para_name))
                        print(
                            f"Found parallelogram: {para_name} with variations: {get_cyclic_variations(para_name)}")

            # Debug print collected facts
            print("\nCollected facts:")
            print("Collinear points:", self.collinear_facts)
            print("Parallel pairs:", self.parallel_pairs)
            print("Points:", list(self.points.keys()))

            # Process theorem sequence
            if 'THEOREM_SEQUENCE' in sections:
                sequence_text = '\n'.join(sections['THEOREM_SEQUENCE'])
                steps = re.split(r'Step \d+:', sequence_text.strip())
                for step in steps:
                    if not step.strip():
                        continue

                    theorem_match = re.search(r'Theorem:\s*(\w+)\(([^)]+)\)', step)
                    premise_match = re.search(r'Premise:(.*?)(?=Conclusion:|$)', step, re.DOTALL)
                    conclusion_match = re.search(r'Conclusion:\s*(\[.*?\])', step)

                    if theorem_match:
                        theorem_name = theorem_match.group(1)
                        args = [arg.strip() for arg in theorem_match.group(2).split(',')]
                        premise = premise_match.group(1).strip() if premise_match else ""
                        conclusions = eval(conclusion_match.group(1)) if conclusion_match else []

                        print(f"\nProcessing theorem step: {theorem_name}")
                        print(f"Arguments: {args}")
                        print(f"Premise: {premise}")
                        print(f"Conclusions: {conclusions}")

                        # Validate premise before processing
                        is_valid, error = self.validate_theorem_premises(theorem_name, args, premise)
                        if not is_valid:
                            print(f"\nError in {error.tier.name}:")
                            print("=" * 40)
                            print(f"Message: {error.message}")
                            if error.details:
                                print(f"Details: {error.details}")
                            return False

                        # Process theorem
                        error = self.process_theorem_step(theorem_name, args, premise, conclusions)
                        if error:
                            print(f"\nError in {error.tier.name}:")
                            print("=" * 40)
                            print(f"Message: {error.message}")
                            if error.details:
                                print(f"Details: {error.details}")
                            return False

                # Parse goal and verify
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

                        # Print current state before verification
                        self.print_current_state()

                        # Try to verify the goal
                        if not self.verify_goal_angle(goal_angle[0], goal_angle[1], goal_angle[2], expected_answer):
                            print(f"\nError in {ErrorTier.TIER3_GOAL_NOT_REACHED.name}:")
                            print("=" * 40)
                            print("Failed to reach the goal")
                            return False
                        return True

                print("Error: Missing required sections in proof")
                return False

        except Exception as e:
            print(f"Error during proof verification: {str(e)}")
            import traceback
            traceback.print_exc()
            return False

    def process_theorem_step(self, theorem_name: str, args: List[str], premise: str, conclusions: List[str]) -> \
    Optional[GeometricError]:
        """Process a single theorem step and return error if any"""
        print(f"\nProcessing {theorem_name} with args: {args}")

        # First validate theorem name
        valid_theorems = [
            "parallelogram_property_opposite_angle_equal",
            "adjacent_complementary_angle",
            "parallel_property_alternate_interior_angle",
            "angle_addition"
        ]
        if theorem_name not in valid_theorems:
            return GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL,
                message=f"Unknown theorem: {theorem_name}",
                details=f"Valid theorems are: {valid_theorems}"
            )

        # Process parallelogram theorem
        if theorem_name == "parallelogram_property_opposite_angle_equal":
            if len(args) < 2:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid number of arguments",
                    details="Expected at least 2 arguments for parallelogram theorem"
                )

            # Check parallelogram premise
            if "Parallelogram" not in premise:
                return GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing parallelogram declaration in premise",
                    details="Parallelogram theorem requires Parallelogram() in premise"
                )

            # Get parallelogram points and directly add the angle equality
            angle1_points = "DAB"  # First opposite angle
            angle2_points = "BCD"  # Second opposite angle

            try:
                angle1 = self.add_angle(angle1_points[0], angle1_points[1], angle1_points[2])
                angle2 = self.add_angle(angle2_points[0], angle2_points[1], angle2_points[2])
                self.solver.add(angle1 == angle2)
                print(f"Added equality: angle_{angle1_points} = angle_{angle2_points}")
            except Exception as e:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Failed to create angles",
                    details=str(e)
                )

        # Process adjacent complementary angle theorem
        elif theorem_name == "adjacent_complementary_angle":
            if len(args) < 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid number of arguments",
                    details="Expected at least 3 arguments for adjacent complementary angle theorem"
                )

            # Check collinearity premise
            if "Collinear" not in premise:
                return GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing collinearity in premise",
                    details="Adjacent complementary angle theorem requires Collinear() in premise"
                )

            angle1_points = args[1]  # BCD
            angle2_points = args[2]  # DCE

            if len(angle1_points) != 3 or len(angle2_points) != 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid angle format",
                    details="Each angle must be specified by exactly 3 points"
                )

            try:
                v = angle1_points[1]  # Common vertex
                angle1 = self.add_angle(angle1_points[0], v, angle1_points[2])
                angle2 = self.add_angle(angle2_points[0], v, angle2_points[2])
                self.solver.add(angle1 + angle2 == 180)
                print(f"Added supplementary relationship: {angle1_points} + {angle2_points} = 180")
            except Exception as e:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Failed to create angles",
                    details=str(e)
                )

        # Process alternate interior angles from parallel lines
        elif theorem_name == "parallel_property_alternate_interior_angle":
            if len(args) < 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid number of arguments",
                    details="Expected at least 3 arguments for parallel property theorem"
                )

            # Check parallel lines premise
            if "ParallelBetweenLine" not in premise:
                return GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing parallel lines in premise",
                    details="Parallel property theorem requires ParallelBetweenLine() in premise"
                )

            line1 = args[1]  # CD
            line2 = args[2]  # AB

            if len(line1) != 2 or len(line2) != 2:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid line format",
                    details="Each line must be specified by exactly 2 points"
                )

            try:
                angle1 = self.add_angle(line1[1], line1[0], line2[0])  # DCB
                angle2 = self.add_angle(line2[0], line2[1], line1[0])  # ABC
                self.solver.add(angle1 == angle2)
                print(f"Added parallel line angle equality: {line1} || {line2}")
            except Exception as e:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Failed to create angles",
                    details=str(e)
                )

        # Process angle addition
        elif theorem_name == "angle_addition":
            if len(args) < 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid number of arguments",
                    details="Expected at least 3 arguments for angle addition theorem"
                )

            total_points = args[1]  # Total angle points
            summand1_points = args[2]  # First angle to add
            summand2_points = args[3] if len(args) > 3 else None  # Second angle to add

            if len(total_points) != 3 or len(summand1_points) != 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid angle format",
                    details="Each angle must be specified by exactly 3 points"
                )

            try:
                total_angle = self.add_angle(total_points[0], total_points[1], total_points[2])
                angle1 = self.add_angle(summand1_points[0], summand1_points[1], summand1_points[2])

                if summand2_points and len(summand2_points) == 3:
                    angle2 = self.add_angle(summand2_points[0], summand2_points[1], summand2_points[2])
                    self.solver.add(total_angle == angle1 + angle2)
                    print(f"Added angle addition: {total_points} = {summand1_points} + {summand2_points}")
            except Exception as e:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Failed to create angles",
                    details=str(e)
                )

        return None
def get_cyclic_variations(para_name: str) -> Set[str]:
    """Get all cyclic variations of a parallelogram name"""
    variations = set()
    n = len(para_name)
    # Add all rotations
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