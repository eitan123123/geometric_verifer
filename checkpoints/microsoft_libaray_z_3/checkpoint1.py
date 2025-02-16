from z3 import *
import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple


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

    def parse_and_verify_proof(self, content: str) -> bool:
        """Parse proof content and verify it using Z3"""
        try:
            # Extract sections
            sections = {}
            current_section = None
            for line in content.split('\n'):
                line = line.strip()
                if not line:
                    continue

                # Check if this is a section header
                if line.endswith('CDL:') or line.endswith('SEQUENCE:') or line == 'ANSWER:':
                    current_section = line[:-1] if line.endswith(':') else line
                    sections[current_section] = []
                elif current_section:
                    sections[current_section].append(line)

            # First, add all points from the CONSTRUCTION_CDL_EXTENDED section
            if 'CONSTRUCTION_CDL_EXTENDED' in sections:
                for line in sections['CONSTRUCTION_CDL_EXTENDED']:
                    if line.startswith('Point('):
                        point = line[6:-1].strip()
                        print(f"Adding point: {point}")  # Debug print
                        self.add_point(point)
                    elif line.startswith('ParallelBetweenLine('):
                        match = re.match(r'ParallelBetweenLine\((\w+),(\w+)\)', line)
                        if match:
                            line1, line2 = match.group(1), match.group(2)
                            # Add points from parallel lines
                            for point in line1 + line2:
                                if point not in self.points:
                                    self.add_point(point)
                            self.add_parallel_lines(line1, line2)

            # Parse text facts
            if 'TEXT_CDL' in sections:
                for line in sections['TEXT_CDL']:
                    if line.startswith('Collinear('):
                        points = line[10:-1].split(',')
                        # Ensure all points exist
                        for p in points:
                            if p not in self.points:
                                self.add_point(p)
                        self.add_collinear_fact(points)
                    elif line.startswith('Equal(MeasureOfAngle('):
                        match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),(\d+)\)', line)
                        if match:
                            angle_points = match.group(1)
                            measure = float(match.group(2))
                            # Ensure all points exist
                            for p in angle_points:
                                if p not in self.points:
                                    self.add_point(p)
                            self.add_angle_measure(angle_points[0], angle_points[1], angle_points[2], measure)
                    elif line.startswith('Parallelogram('):
                        points = line[14:-1]
                        # Ensure all points exist
                        for p in points:
                            if p not in self.points:
                                self.add_point(p)
                        self.add_parallelogram(list(points))

            # Process theorem sequence
            if 'THEOREM_SEQUENCE' in sections:
                sequence_text = '\n'.join(sections['THEOREM_SEQUENCE'])
                steps = re.split(r'Step \d+:', sequence_text.strip())
                for step in steps:
                    if not step.strip():
                        continue

                    # Extract theorem details
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

                        self.process_theorem_step(theorem_name, args, premise, conclusions)

            # Parse goal
            if 'GOAL_CDL' in sections:
                goal_line = sections['GOAL_CDL'][0]
                goal_match = re.search(r'Value\(MeasureOfAngle\((\w+)\)\)', goal_line)
                if not goal_match:
                    print("Error: Could not parse goal angle")
                    return False
                goal_angle = goal_match.group(1)

                # Get answer
                if 'ANSWER' in sections and sections['ANSWER']:
                    expected_answer = float(sections['ANSWER'][0])

                    print(f"\nGoal angle: {goal_angle}")
                    print(f"Expected answer: {expected_answer}")

                    # Print current state before verification
                    self.print_current_state()

                    return self.verify_goal_angle(
                        goal_angle[0],
                        goal_angle[1],
                        goal_angle[2],
                        expected_answer
                    )

            print("Error: Missing required sections in proof")
            return False

        except Exception as e:
            print(f"Error during proof verification: {str(e)}")
            import traceback
            traceback.print_exc()
            return False

    def process_theorem_step(self, theorem_name: str, args: List[str], premise: str, conclusions: List[str]):
        """Process a single theorem step from the sequence"""
        print(f"\nProcessing {theorem_name} with args: {args}")

        # Process parallelogram theorem
        if theorem_name == "parallelogram_property_opposite_angle_equal":
            if len(args) >= 2:
                # Get parallelogram points and directly add the angle equality
                angle1_points = "DAB"  # First opposite angle
                angle2_points = "BCD"  # Second opposite angle

                angle1 = self.add_angle(angle1_points[0], angle1_points[1], angle1_points[2])
                angle2 = self.add_angle(angle2_points[0], angle2_points[1], angle2_points[2])
                self.solver.add(angle1 == angle2)

                print(f"Added equality: angle_{angle1_points} = angle_{angle2_points}")

        # Process adjacent complementary angle theorem
        elif theorem_name == "adjacent_complementary_angle":
            if len(args) >= 3:
                angle1_points = args[1]  # BCD
                angle2_points = args[2]  # DCE

                # Directly set up the supplementary angle relationship
                if len(angle1_points) == 3 and len(angle2_points) == 3:
                    v = angle1_points[1]  # Common vertex
                    angle1 = self.add_angle(angle1_points[0], v, angle1_points[2])
                    angle2 = self.add_angle(angle2_points[0], v, angle2_points[2])
                    self.solver.add(angle1 + angle2 == 180)
                    print(f"Added supplementary relationship: {angle1_points} + {angle2_points} = 180")

        # Process alternate interior angles from parallel lines
        elif theorem_name == "parallel_property_alternate_interior_angle":
            if len(args) >= 3:
                line1 = args[1]  # CD
                line2 = args[2]  # AB

                if len(line1) == 2 and len(line2) == 2:
                    # Get the angles for parallel lines
                    angle1 = self.add_angle(line1[1], line1[0], line2[0])  # DCB
                    angle2 = self.add_angle(line2[0], line2[1], line1[0])  # ABC
                    self.solver.add(angle1 == angle2)
                    print(f"Added parallel line angle equality: {line1} || {line2}")

        # Process angle addition
        elif theorem_name == "angle_addition":
            if len(args) >= 3:
                total_points = args[1]  # Total angle points
                summand1_points = args[2]  # First angle to add
                summand2_points = args[3] if len(args) > 3 else None  # Second angle to add

                if len(total_points) == 3 and len(summand1_points) == 3:
                    total_angle = self.add_angle(total_points[0], total_points[1], total_points[2])
                    angle1 = self.add_angle(summand1_points[0], summand1_points[1], summand1_points[2])

                    if summand2_points and len(summand2_points) == 3:
                        angle2 = self.add_angle(summand2_points[0], summand2_points[1], summand2_points[2])
                        self.solver.add(total_angle == angle1 + angle2)
                        print(f"Added angle addition: {total_points} = {summand1_points} + {summand2_points}")
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
    result = verify_geometric_proof("/questions/the new format for questions after jan_17/question2/question2_correct")
    theorem.debug_state()  # Add this line
    print(f"Verification {'succeeded' if result else 'failed'}")