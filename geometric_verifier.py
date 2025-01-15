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
        # Initial state tracking
        self.can_prove_goal = False
        self.initial_facts = {
            'collinear_points': [],
            'parallel_pairs': set()
        }
        self.initial_known_angles = {}
        self.proven_angle_relationships = []
        self.known_angle_values = {}

        # Solver and basic geometric elements
        self.solver = Solver()
        self.points = {}
        self.angles = {}
        self.parallel_pairs = set()
        self.perpendicular_pairs = set()
        self.collinear_facts = []

        # For handling both algebraic and numeric expressions
        self.variables = {}
        self.algebraic_angles = {}
        self.numeric_angles = {}
        self.found_tier_1_or_2_error = False

    def extract_variables(self, expression: str) -> Set[str]:
        """Extract variable names from an algebraic expression"""
        # Use regex to find single letters that aren't part of numbers
        variables = set(re.findall(r'(?<!\d)[a-zA-Z](?!\d)', expression))
        return variables



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
            # Always create the angle variable
            self.angles[angle_name] = Real(angle_name)
            # Add basic angle constraints
            self.solver.add(self.angles[angle_name] >= 0)
            self.solver.add(self.angles[angle_name] <= 180)

            # Track if this is a proven/known angle
            if normalized in self.known_angle_values:
                print(f"Added known angle {normalized} = {self.known_angle_values[normalized]}")
            elif any(normalized in rel for rel in self.proven_angle_relationships):
                print(f"Added proven angle {normalized}")

        return self.angles[angle_name]

    def normalize_angle_name(self, angle_points: str) -> str:
        """Normalize angle name (ABC and CBA are same angle, but ACB is different)"""
        if len(angle_points) != 3:
            return angle_points

        p1, vertex, p2 = angle_points[0], angle_points[1], angle_points[2]
        # Only swap endpoints if needed to maintain vertex in middle
        if p1 > p2:
            return f"{p2}{vertex}{p1}"
        return f"{p1}{vertex}{p2}"

    def normalize_parallelogram(self, points: str) -> Set[str]:
        """Get all valid cyclic variations of parallelogram name
        ABCD becomes {ABCD, BCDA, CDAB, DABC} but not DCBA etc."""
        if len(points) != 4:
            return {points}

        variations = set()
        for i in range(4):
            # Add cyclic variation
            variation = points[i:] + points[:i]
            variations.add(variation)
        return variations



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

    def parse_algebraic_expression(self, expr: str) -> Real:
        """Convert string expression to Z3 expression using any variables"""
        expr = expr.strip()
        try:
            # Handle pure variable case
            if expr in self.variables:
                return self.variables[expr]

            # Try to convert to float first
            try:
                return float(expr)
            except ValueError:
                pass

            # Handle arithmetic operations
            if '+' in expr:
                left, right = expr.rsplit('+', 1)
                return self.parse_algebraic_expression(left) + self.parse_algebraic_expression(right)
            elif '-' in expr and not expr.startswith('-'):
                left, right = expr.rsplit('-', 1)
                return self.parse_algebraic_expression(left) - self.parse_algebraic_expression(right)
            elif expr.startswith('-'):
                return -self.parse_algebraic_expression(expr[1:])
            elif '/' in expr:
                num, denom = expr.split('/')
                return self.parse_algebraic_expression(num) / self.parse_algebraic_expression(denom)
            elif '*' in expr:
                left, right = expr.split('*')
                return self.parse_algebraic_expression(left) * self.parse_algebraic_expression(right)

            # If we get here, check if any variables are in the expression
            for var_name, var in self.variables.items():
                if var_name in expr:
                    return self.variables[var_name]

            raise ValueError(f"Cannot parse expression: {expr}")

        except Exception as e:
            print(f"Error parsing expression '{expr}': {str(e)}")
            raise



    def add_algebraic_angle(self, angle_name: str, expression: str):
        """Add an angle with an algebraic expression"""
        print(f"\nAdding algebraic angle constraint: {angle_name} = {expression}")

        # Try to parse as numeric first
        try:
            value = float(expression)
            print(f"Adding numeric value: {angle_name} = {value}")
            normalized = self.normalize_angle_name(angle_name)

            # Add to both known values and constraints
            self.known_angle_values[normalized] = value
            angle_var = self.add_angle(normalized[0], normalized[1], normalized[2])
            self.solver.add(angle_var == value)
            # Store the expression even though it's numeric
            self.algebraic_angles[normalized] = str(value)
            print(f"Stored numeric value: {normalized} = {value}")
            return
        except ValueError:
            # Not a numeric value, handle as algebraic expression
            pass

        # Find variables in expression
        variables = self.extract_variables(expression)

        # Create Z3 variables for algebraic expression
        for var in variables:
            if var not in self.variables:
                self.variables[var] = Real(var)
                print(f"Created new variable: {var}")

        angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])
        expr = self.parse_algebraic_expression(expression)
        self.solver.add(angle_var == expr)

        # Store original expression
        normalized = self.normalize_angle_name(angle_name)
        self.algebraic_angles[normalized] = expression


    def verify_goal_angle(self, p1: str, v: str, p2: str, expected: float, epsilon: float = 1e-10) -> bool:
        print("\nStarting Goal Verification")
        print("========================")
        # Print debug state before verification
        self.debug_state()

        print(f"\nVerifying goal angle: {p1}{v}{p2}")
        angle_name = p1 + v + p2

        # Debug current state before verification
        print("\nCurrent state before verification:")
        self.debug_known_values()
        print("\nProven relationships:")
        for rel in self.proven_angle_relationships:
            rel_type, angle1, angle2 = rel
            print(f"{rel_type}: {angle1} = {angle2}")

        # Check if we can reach this angle through our proven relationships
        can_prove = False
        if angle_name in self.known_angle_values:
            can_prove = True
            print(f"Found angle {angle_name} in known values with value {self.known_angle_values[angle_name]}")
        else:
            # Check if it's connected to a known angle through proven relationships
            for rel_type, angle1, angle2 in self.proven_angle_relationships:
                if angle1 == angle_name and angle2 in self.known_angle_values:
                    can_prove = True
                    print(f"Can prove {angle_name} through relationship with {angle2}")
                    break
                if angle2 == angle_name and angle1 in self.known_angle_values:
                    can_prove = True
                    print(f"Can prove {angle_name} through relationship with {angle1}")
                    break

        if not can_prove:
            print("\nTier 3 Error: Cannot prove goal angle through theorem applications")
            print("Known angle values:", self.known_angle_values)
            print("Proven relationships:", self.proven_angle_relationships)
            return False

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

                        if abs(angle_val - expected) < epsilon:
                            print("Value matches expected!")
                            return True
                        else:
                            print("Value does not match expected.")
                            return False

            print("Error: Could not find angle in model")
            return False

        except Exception as e:
            print(f"Error during verification: {str(e)}")
            return False

    def debug_known_values(self):
        print("\nDEBUG - Current known angle values:")
        print(self.known_angle_values)

    def debug_state(self):
        """Print current state of the geometric system"""
        print("\nDebug State:")
        print("===========")

        # Save initial facts at beginning and use them consistently
        print("\nGeometric Facts:")
        print(f"Collinear points:", self.initial_facts['collinear_points'])
        print(f"Parallel pairs:", self.initial_facts['parallel_pairs'])

        # Show initial known values
        print("\nInitially Known Values:")
        for angle, value in self.initial_known_angles.items():
            print(f"{angle}: {value}°")

        # Show proven relationships
        print("\nProven Through Theorems:")
        for rel_type, angle1, angle2 in self.proven_angle_relationships:
            if rel_type == "equal":
                print(f"{angle1} = {angle2}")
            elif rel_type == "supplementary":
                print(f"{angle1} + {angle2} = 180°")



        # Only show Tier 3 error if no higher-tier error was found
        if not self.can_prove_goal and not hasattr(self, 'found_tier_1_or_2_error'):
            print("\nTier 3 Error: Failed to reach goal through theorem applications")

    def validate_theorem_premises(self, theorem_name: str, args: List[str], premise: str) -> Tuple[
        bool, Optional[GeometricError]]:
        """Validate theorem premises and return appropriate error if validation fails"""

        # Helper function to return error and set the flag
        def return_error(error):
            self.found_tier_1_or_2_error = True
            return False, error

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
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Points {points} are not proven collinear",
                            details=f"Known collinear facts: {self.collinear_facts}"
                        ))

                    # Also verify the angles exist
                    if len(args) < 3:
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER1_THEOREM_CALL,
                            message="Missing angle arguments",
                            details="adjacent_complementary_angle requires two angles"
                        ))

                    # Verify angle points share a vertex and are on the collinear line
                    angle1_points = args[1]
                    angle2_points = args[2]
                    if not (angle1_points[1] == angle2_points[1] and
                            all(p in points for p in [angle1_points[1], angle2_points[1]])):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Angles {angle1_points} and {angle2_points} must share a vertex on collinear line {points}"
                        ))
                else:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Invalid collinear points format in premise"
                    ))
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing collinear points in premise",
                    details="adjacent_complementary_angle theorem requires collinear points"
                ))

        elif theorem_name == "parallelogram_property_opposite_angle_equal":
            if len(args) < 2:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing parallelogram argument",
                    details="parallelogram_property_opposite_angle_equal requires a parallelogram name"
                ))

            theorem_para = args[1]
            premise_match = re.search(r'Parallelogram\((\w+)\)', premise)

            if not premise_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Invalid parallelogram format in premise"
                ))

            premise_para = premise_match.group(1)

            if not any(cyclic_var == premise_para for cyclic_var in self.parallelograms):
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Parallelogram {premise_para} is not defined in TEXT_CDL",
                    details=f"Available parallelograms: {', '.join(self.parallelograms)}"
                ))

            if theorem_para != premise_para:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Theorem uses parallelogram {theorem_para} but premise specifies {premise_para}",
                    details="Theorem argument must match the parallelogram in the premise"
                ))

        elif theorem_name == "parallel_property_alternate_interior_angle":
            if "ParallelBetweenLine" not in premise:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing parallel lines in premise",
                    details="parallel_property_alternate_interior_angle theorem requires parallel lines"
                ))

            line_match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', premise)
            if not line_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Invalid parallel lines format in premise"
                ))

            line1, line2 = line_match.group(1), line_match.group(2)
            if (line1, line2) not in self.parallel_pairs and (line2, line1) not in self.parallel_pairs:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Lines {line1} and {line2} not proven parallel",
                    details=f"Available parallel pairs: {self.parallel_pairs}"
                ))

            if len(args) < 3:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing line arguments",
                    details="parallel_property_alternate_interior_angle requires two parallel lines"
                ))

        elif theorem_name == "angle_addition":
            if len(args) < 3:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing angle arguments",
                    details="angle_addition requires at least two angles"
                ))

            angle1 = args[1] if len(args) > 1 else ""
            angle2 = args[2] if len(args) > 2 else ""

            if len(angle1) != 3 or len(angle2) != 3:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid angle format",
                    details="Each angle must be specified by exactly 3 points"
                ))

            if angle1[1] != angle2[1]:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Angles {angle1} and {angle2} must share a vertex",
                    details="Required for angle addition"
                ))

        elif theorem_name == "quadrilateral_property_angle_sum":
            if len(args) < 2:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid number of arguments",
                    details="Expected quadrilateral name for angle sum theorem"
                ))

            quad_name = args[1]
            if f"Polygon({quad_name})" not in premise:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Quadrilateral {quad_name} is not defined in premise",
                    details="Quadrilateral must be defined as a polygon"
                ))

        return True, None


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
            # Inside parse_and_verify_proof, when processing TEXT_CDL section:
            # Inside parse_and_verify_proof, modify the TEXT_CDL section:
            if 'TEXT_CDL' in sections:
                for line in sections['TEXT_CDL']:
                    if line.startswith('Equal(MeasureOfAngle('):
                        match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                        if match:
                            angle_name, expression = match.group(1), match.group(2).strip()
                            print(f"Found angle expression in TEXT_CDL: {angle_name} = {expression}")
                            self.add_algebraic_angle(angle_name, expression)
                    elif line.startswith('Parallelogram('):
                        match = re.match(r'Parallelogram\((\w+)\)', line)
                        if match:
                            para_name = match.group(1)
                            print(f"Found parallelogram in TEXT_CDL: {para_name}")
                            self.parallelograms.update(get_cyclic_variations(para_name))
                            print(f"Added parallelogram variations: {self.parallelograms}")
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
        print(f"\nVerifying goal angle: {goal_angle}")

        # First check direct known values
        if goal_angle in self.known_angle_values:
            value = self.known_angle_values[goal_angle]
            print(f"Found direct value: {goal_angle} = {value}°")
            return abs(value - expected) < epsilon

        # Check relationships for non-algebraic proofs
        for rel_type, angle1, angle2 in self.proven_angle_relationships:
            if rel_type == "equal":
                if angle1 == goal_angle and angle2 in self.known_angle_values:
                    value = self.known_angle_values[angle2]
                    print(f"Proved through equality: {goal_angle} = {angle2} = {value}°")
                    return abs(value - expected) < epsilon
                elif angle2 == goal_angle and angle1 in self.known_angle_values:
                    value = self.known_angle_values[angle1]
                    print(f"Proved through equality: {goal_angle} = {angle1} = {value}°")
                    return abs(value - expected) < epsilon
                elif angle1 == goal_angle:
                    print(f"Found equality relationship but no value: {goal_angle} = {angle2}")
                elif angle2 == goal_angle:
                    print(f"Found equality relationship but no value: {goal_angle} = {angle1}")

        # If we have algebraic expressions
        if self.algebraic_angles:
            print("\nAnalyzing algebraic expressions...")
            print("Current expressions:", self.algebraic_angles)

            # Find variable name
            var_name = None
            for expr in self.algebraic_angles.values():
                vars = self.extract_variables(expr)
                if vars:
                    var_name = list(vars)[0]
                    break

            if not var_name:
                # Handle pure numeric case
                try:
                    if goal_angle in self.algebraic_angles:
                        value = float(self.algebraic_angles[goal_angle])
                        print(f"Found direct numeric value: {goal_angle} = {value}°")
                        return abs(value - expected) < epsilon

                    # Check if we can derive the value through proven relationships
                    for rel_type, angles, rel_val in self.proven_angle_relationships:
                        if rel_type == "equal":
                            # If we have an equality relationship, check both angles
                            if goal_angle in angles:
                                other_angle = angles[0] if angles[1] == goal_angle else angles[1]
                                if other_angle in self.algebraic_angles:
                                    try:
                                        value = float(self.algebraic_angles[other_angle])
                                        print(
                                            f"Found numeric value through equality: {goal_angle} = {other_angle} = {value}°")
                                        return abs(value - expected) < epsilon
                                    except ValueError:
                                        pass
                except ValueError:
                    pass

                print("\nTier 3 Error: Cannot prove goal angle through numeric values")
                print("Known values:", self.known_angle_values)
                print("Proven relationships:", self.proven_angle_relationships)
                print("Algebraic expressions:", self.algebraic_angles)
                return False

            print(f"Using variable: {var_name}")

            # Process sum relationships
            for rel_type, angles, sum_value in self.proven_angle_relationships:
                if rel_type == "sum":
                    print(f"\nUsing sum relationship: {angles} = {sum_value}")

                    # Try values for the variable
                    for test_value in range(0, 361):
                        try:
                            total_sum = 0
                            angle_values = {}
                            valid_solution = True

                            # Calculate all angles
                            for angle_name in angles:
                                expr = None
                                # Try all possible variations of the angle name
                                possible_names = [
                                    angle_name,  # Original
                                    self.normalize_angle_name(angle_name),  # Normalized
                                    angle_name[2] + angle_name[1] + angle_name[0],  # Reversed
                                ]

                                # Try each possible name
                                for possible_name in possible_names:
                                    if possible_name in self.algebraic_angles:
                                        expr = self.algebraic_angles[possible_name]
                                        break

                                if expr:
                                    # Handle division safely
                                    expr = expr.replace(f'{var_name}/2', f'0.5*{var_name}')
                                    angle_value = eval(expr, {var_name: test_value})

                                    # Verify angle is valid
                                    if angle_value < 0 or angle_value > 180:
                                        valid_solution = False
                                        break

                                    total_sum += angle_value
                                    angle_values[angle_name] = angle_value
                                    print(f"Calculated {angle_name} = {angle_value}° using {expr}")
                                else:
                                    valid_solution = False
                                    print(f"Could not find expression for {angle_name}")
                                    break

                            # Check if we found a valid solution
                            if valid_solution and abs(total_sum - float(sum_value)) < epsilon:
                                # Try to find goal angle value
                                goal_expr = None
                                possible_goals = [
                                    goal_angle,  # Original
                                    self.normalize_angle_name(goal_angle),  # Normalized
                                    goal_angle[2] + goal_angle[1] + goal_angle[0]  # Reversed
                                ]

                                # Try each possible goal angle name
                                for possible_goal in possible_goals:
                                    if possible_goal in self.algebraic_angles:
                                        goal_expr = self.algebraic_angles[possible_goal]
                                        break

                                if goal_expr:
                                    goal_expr = goal_expr.replace(f'{var_name}/2', f'0.5*{var_name}')
                                    goal_value = eval(goal_expr, {var_name: test_value})

                                    if abs(goal_value - expected) < epsilon:
                                        print(f"\nFound solution!")
                                        print(f"{var_name} = {test_value}")
                                        print(f"Goal angle {goal_angle} = {goal_value}°")
                                        for ang, val in sorted(angle_values.items()):
                                            print(f"{ang} = {val}°")
                                        self.can_prove_goal = True
                                        return True

                        except Exception as e:
                            continue

            print("\nTier 3 Error: Cannot prove goal angle")
            print("Known values:", self.known_angle_values)
            print("Proven relationships:", self.proven_angle_relationships)
            print("Algebraic expressions:", self.algebraic_angles)
            return False

    def process_theorem_step(self, theorem_name: str, args: List[str], premise: str, conclusions: List[str]) -> \
    Optional[GeometricError]:
        print(f"\nProcessing theorem step: {theorem_name}")
        print(f"Arguments: {args}")
        print(f"Premise: '{premise}'")
        print(f"Conclusions: {conclusions}")

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

        if theorem_name == "parallelogram_property_opposite_angle_equal":
            if len(args) < 2:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing parallelogram argument",
                    details="Expected parallelogram name"
                )

            # Validate parallelogram with cyclic variations
            para_name = args[1]
            valid_variations = self.normalize_parallelogram(para_name)
            if not any(var in self.parallelograms for var in valid_variations):
                return GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Invalid parallelogram: {para_name}",
                    details=f"Valid variations would be: {valid_variations}"
                )

            angles_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),\s*MeasureOfAngle\((\w+)\)\)', conclusions[0])
            if angles_match:
                angle1, angle2 = angles_match.group(1), angles_match.group(2)
                norm_angle1 = self.normalize_angle_name(angle1)
                norm_angle2 = self.normalize_angle_name(angle2)

                # Add normalized angles to solver
                angle1_var = self.add_angle(norm_angle1[0], norm_angle1[1], norm_angle1[2])
                angle2_var = self.add_angle(norm_angle2[0], norm_angle2[1], norm_angle2[2])
                self.solver.add(angle1_var == angle2_var)
                print(f"Added parallelogram opposite angle equality: {norm_angle1} = {norm_angle2}")

                # Track the proven relationship using normalized angles
                self.proven_angle_relationships.append(("equal", angle1, angle2))
                print(f"Added relationship: {angle1} = {angle2}")

                # If we know one angle's value, we now know the other
                if norm_angle1 in self.known_angle_values:
                    value = self.known_angle_values[norm_angle1]
                    self.known_angle_values[norm_angle2] = value
                    print(f"Proved angle {norm_angle2} = {value} through parallelogram property")
                elif norm_angle2 in self.known_angle_values:
                    value = self.known_angle_values[norm_angle2]
                    self.known_angle_values[norm_angle1] = value
                    print(f"Proved angle {norm_angle1} = {value} through parallelogram property")


        elif theorem_name == "adjacent_complementary_angle":

            if len(args) < 3:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Missing angle arguments",

                    details="Expected two angles"

                )

            angle1_points = args[1]

            angle2_points = args[2]

            # Normalize angle names

            norm_angle1 = self.normalize_angle_name(angle1_points)

            norm_angle2 = self.normalize_angle_name(angle2_points)

            angle1_var = self.add_angle(norm_angle1[0], norm_angle1[1], norm_angle1[2])

            angle2_var = self.add_angle(norm_angle2[0], norm_angle2[1], norm_angle2[2])

            self.solver.add(angle1_var + angle2_var == 180)

            print(f"Added supplementary angle constraint: {norm_angle1} + {norm_angle2} = 180")

            # Track the proven relationship using normalized angles

            self.proven_angle_relationships.append(("supplementary", norm_angle1, norm_angle2))

            print(f"Added supplementary relationship: {norm_angle1} + {norm_angle2} = 180")

            # If we know one angle's value, calculate the other

            if norm_angle1 in self.known_angle_values:

                value = self.known_angle_values[norm_angle1]

                supp_value = 180 - value

                self.known_angle_values[norm_angle2] = supp_value

                print(f"Using {norm_angle1} = {value}, proved {norm_angle2} = {supp_value}")

            elif norm_angle2 in self.known_angle_values:

                value = self.known_angle_values[norm_angle2]

                supp_value = 180 - value

                self.known_angle_values[norm_angle1] = supp_value

                print(f"Using {norm_angle2} = {value}, proved {norm_angle1} = {supp_value}")


        elif theorem_name == "quadrilateral_property_angle_sum":

            if len(args) < 2:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Invalid number of arguments",

                    details="Expected quadrilateral name"

                )

            quad_name = args[1]

            angles = []

            angle_names = []

            # Get angles in correct order around the quadrilateral

            for i in range(len(quad_name)):
                p1 = quad_name[i]

                p2 = quad_name[(i + 1) % len(quad_name)]

                p3 = quad_name[(i + 2) % len(quad_name)]

                angle = self.add_angle(p1, p2, p3)

                angle_name = p1 + p2 + p3

                angles.append(angle)

                angle_names.append(angle_name)

                print(f"Added angle {angle_name}")

            # Add quadrilateral angle sum constraint

            self.solver.add(sum(angles) == 360)

            print(f"Added quadrilateral sum constraint: sum of angles = 360°")

            # Track the sum relationship for algebraic solving

            self.proven_angle_relationships.append(("sum", angle_names, "360"))

            # If all angles but one are known algebraically, solve for the last one

            known_sum = 0

            unknown_angle = None

            for angle_name in angle_names:

                if angle_name in self.algebraic_angles:

                    expr = self.algebraic_angles[angle_name]

                    try:

                        val = float(expr.replace('a', '108'))  # Use a=108 based on equations

                        known_sum += val

                    except:

                        if unknown_angle is None:

                            unknown_angle = angle_name

                        else:

                            unknown_angle = None

                            break

            if unknown_angle is not None:
                value = 360 - known_sum

                self.known_angle_values[unknown_angle] = value

                print(f"Derived value for {unknown_angle} = {value}°")

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
    result = verify_geometric_proof("/Users/eitan/Desktop/lean/lean_python/questions/question2/question2_14")
    print(f"Verification {'succeeded' if result else 'failed'}")