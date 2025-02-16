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

class GeometricTheorem:
    def __init__(self):
        # Initial state tracking
        self.can_prove_goal = False
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
        self.found_tier_1_or_2_error = False

        # Add these new attributes for length handling
        self.lengths = {}  # Store line lengths
        self.known_length_values = {}  # Store known length values
        self.proven_length_relationships = []
        self.right_triangles = set()  # Add this line

        self.similar_triangles = []  # Store pairs of similar triangles
        self.triangle_perimeters = {}  # Store triangle perimeter values
        self.triangle_ratios = {}  # Store ratios between similar triangles



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

    def add_length(self, p1: str, p2: str) -> Real:
        """Add a length variable to Z3 solver"""
        # Normalize the line name (AB and BA are same)
        normalized = self.normalize_line_name(p1 + p2)
        length_name = f"length_{normalized}"

        if length_name not in self.lengths:
            self.lengths[length_name] = Real(length_name)
            # Add basic length constraints (non-negative)
            self.solver.add(self.lengths[length_name] >= 0)

            # Check if we know this length
            if normalized in self.known_length_values:
                self.solver.add(self.lengths[length_name] == self.known_length_values[normalized])
                print(f"Added known length {normalized} = {self.known_length_values[normalized]}")

        return self.lengths[length_name]

    def normalize_triangle_name(self, triangle: str) -> str:
        """Normalize triangle name (ABC, BCA, and CAB are the same)"""
        if len(triangle) != 3:
            return triangle
        rotations = [triangle[i:] + triangle[:i] for i in range(3)]
        return min(rotations)

    def are_triangles_similar(self, tri1: str, tri2: str) -> bool:
        """Check if two triangles are recorded as similar"""
        normalized = self.normalize_similar_triangles(tri1, tri2)
        if not normalized:
            return False
        norm1, norm2 = normalized
        return (norm1, norm2) in self.similar_triangles or (norm2, norm1) in self.similar_triangles

    def add_similar_triangles(self, tri1: str, tri2: str):
        """Record that two triangles are similar"""
        normalized = self.normalize_similar_triangles(tri1, tri2)
        if normalized:
            norm1, norm2 = normalized
            self.similar_triangles.append((norm1, norm2))
            # Also store reverse order
            self.similar_triangles.append((norm2, norm1))

    def calculate_perimeter(self, triangle: str) -> Optional[Real]:
        """Calculate perimeter of a triangle"""
        if len(triangle) != 3:
            return None

        sides = []
        for i in range(3):
            p1 = triangle[i]
            p2 = triangle[(i + 1) % 3]
            length_var = self.add_length(p1, p2)
            sides.append(length_var)

        return sum(sides)


    def normalize_line_name(self, line_points: str) -> str:
        """Normalize line name (AB and BA are same line)"""
        if len(line_points) != 2:
            return line_points
        return min(line_points, line_points[::-1])

    def add_right_triangle(self, points: str):
        """Add a right triangle with 90° angle"""
        if len(points) != 3:
            return

        # Add the triangle to proven right triangles
        triangle = ''.join(sorted(points))
        self.right_triangles.add(triangle)

        # Add 90° angle constraint
        angle_var = self.add_angle(points[0], points[1], points[2])
        self.solver.add(angle_var == 90)
        self.known_angle_values[points] = 90.0

    def normalize_similar_triangles(self, tri1: str, tri2: str) -> Optional[Tuple[str, str]]:
        """Normalize two similar triangles preserving vertex correspondence
        Returns (normalized_tri1, normalized_tri2) if valid correspondence found, None otherwise
        """
        if len(tri1) != 3 or len(tri2) != 3:
            return None

        # Get all rotations of first triangle
        rotations1 = [tri1[i:] + tri1[:i] for i in range(3)]
        # For each rotation of tri1, tri2 must rotate the same way to preserve correspondence
        for i, rot1 in enumerate(rotations1):
            rot2 = tri2[i:] + tri2[:i]
            # Store the lexicographically smallest pair that preserves correspondence
            if i == 0 or (rot1, rot2) < normalized:
                normalized = (rot1, rot2)

        return normalized

    def normalize_angle_name(self, angle_points: str) -> str:
        """Normalize angle name (ABC and CBA are same angle, but ACB is different)"""
        if len(angle_points) != 3:
            return angle_points

        p1, vertex, p2 = angle_points[0], angle_points[1], angle_points[2]
        # Consider both orientations (DAB and BAD are the same)
        option1 = f"{p1}{vertex}{p2}"
        option2 = f"{p2}{vertex}{p1}"
        # Return the lexicographically smaller option
        return min(option1, option2)

    def normalize_collinear_points(self, points: str) -> str:
        """Normalize collinear points (ABC and CBA are same, but BCA is different)"""
        # Consider both forward and reversed order
        option1 = points
        option2 = points[::-1]
        # Return the lexicographically smaller option
        return min(option1, option2)


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

            # Join points to string and normalize
        points_str = ''.join(points)
        normalized = self.normalize_collinear_points(points_str)
        points = list(normalized)  # Convert back to list
        # For each three consecutive points
        for i in range(len(points) - 2):
            p1, v, p2 = points[i:i + 3]

            # Add points if they don't exist
            for p in [p1, v, p2]:
                if p not in self.points:
                    self.add_point(p)

            # Add straight angle constraint (180°) - use normalized angle
            straight_angle = self.normalize_angle_name(p1 + v + p2)
            angle_var = self.add_angle(straight_angle[0], straight_angle[1], straight_angle[2])
            self.solver.add(angle_var == 180)
            self.known_angle_values[straight_angle] = 180.0

            # Any other point forms supplementary angles with this line
            for q in self.points:
                if q not in [p1, v, p2]:
                    # Create and normalize both angles
                    angle1_name = self.normalize_angle_name(p1 + v + q)
                    angle2_name = self.normalize_angle_name(q + v + p2)

                    # Add the angles to solver using normalized names
                    angle1_var = self.add_angle(angle1_name[0], angle1_name[1], angle1_name[2])
                    angle2_var = self.add_angle(angle2_name[0], angle2_name[1], angle2_name[2])

                    # These angles must be supplementary
                    self.solver.add(angle1_var + angle2_var == 180)

                    # Each angle must be between 0° and 180°
                    self.solver.add(angle1_var > 0)
                    self.solver.add(angle1_var < 180)
                    self.solver.add(angle2_var > 0)
                    self.solver.add(angle2_var < 180)

                    # Track the supplementary relationship
                    self.proven_angle_relationships.append(("supplementary", angle1_name, angle2_name))

                    # Method 1: Check known_angle_values
                    if angle1_name in self.known_angle_values:
                        val = self.known_angle_values[angle1_name]
                        self.known_angle_values[angle2_name] = 180 - val
                    elif angle2_name in self.known_angle_values:
                        val = self.known_angle_values[angle2_name]
                        self.known_angle_values[angle1_name] = 180 - val



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

    def verify_goal_length(self, p1: str, p2: str, expected: float, epsilon: float = 1e-10) -> bool:
        """Verify if a length goal matches expected value"""
        goal_line = p1 + p2
        normalized = self.normalize_line_name(goal_line)

        print(f"\nVerifying length goal: {goal_line}")
        print(f"Expected value: {expected}")
        print(f"Known length values: {self.known_length_values}")
        print(f"Proven length relationships: {self.proven_length_relationships}")

        # Check direct known values
        if normalized in self.known_length_values:
            value = self.known_length_values[normalized]
            return abs(value - expected) < epsilon

        # Check if we can derive it from relationships
        for rel_type, *parts in self.proven_length_relationships:
            if rel_type == "sum":
                line1, line2, total = parts
                if total == normalized and line1 in self.known_length_values and line2 in self.known_length_values:
                    sum_value = self.known_length_values[line1] + self.known_length_values[line2]
                    return abs(sum_value - expected) < epsilon

        return False

    def verify_goal_angle(self, p1: str, v: str, p2: str, expected: float, epsilon: float = 1e-10) -> bool:
        print("\n=== VERIFICATION START ===")
        goal_angle = p1 + v + p2
        print(f"Goal angle: {goal_angle}")
        print(f"Expected value: {expected}°")

        print("\nKNOWN VALUES:")
        for angle, value in self.known_angle_values.items():
            print(f"  {angle} = {value}°")

        print("\nPROVEN RELATIONSHIPS:")
        for rel in self.proven_angle_relationships:
            print(f"  {rel}")

        # Check direct known values
        if goal_angle in self.known_angle_values:
            value = self.known_angle_values[goal_angle]
            print(f"Found direct value: {goal_angle} = {value}°")
            return abs(value - expected) < epsilon

        # Check through relationships
        for rel_type, *parts in self.proven_angle_relationships:
            print(f"\nChecking relationship type: {rel_type}")
            if rel_type == "equal":
                angle1, angle2 = parts
                if goal_angle == angle1 and angle2 in self.known_angle_values:
                    value = self.known_angle_values[angle2]
                    print(f"Found value through equality: {goal_angle} = {angle2} = {value}°")
                    return abs(value - expected) < epsilon
                if goal_angle == angle2 and angle1 in self.known_angle_values:
                    value = self.known_angle_values[angle1]
                    print(f"Found value through equality: {goal_angle} = {angle1} = {value}°")
                    return abs(value - expected) < epsilon
            elif rel_type == "sum":
                angles, total = parts  # ['ECD', 'DCB'], 'ECB'
                print(f"Checking sum relationship: {total} = {angles[0]} + {angles[1]}")

                # If we're looking for first addend
                if goal_angle == angles[0] and total in self.known_angle_values and angles[
                    1] in self.known_angle_values:
                    sum_value = self.known_angle_values[total]
                    known_part = self.known_angle_values[angles[1]]
                    value = sum_value - known_part
                    print(f"Found value through sum: {goal_angle} = {sum_value}° - {known_part}° = {value}°")
                    return abs(value - expected) < epsilon

                # If we're looking for second addend
                if goal_angle == angles[1] and total in self.known_angle_values and angles[
                    0] in self.known_angle_values:
                    sum_value = self.known_angle_values[total]
                    known_part = self.known_angle_values[angles[0]]
                    value = sum_value - known_part
                    print(f"Found value through sum: {goal_angle} = {sum_value}° - {known_part}° = {value}°")
                    return abs(value - expected) < epsilon

        print("\nVERIFICATION FAILED")
        print("Could not prove goal angle value")
        print(f"Known values: {self.known_angle_values}")
        print(f"Available relationships: {self.proven_angle_relationships}")
        return False

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
                    # Normalize the points from premise
                    normalized_premise_points = self.normalize_collinear_points(points)

                    # Check if these normalized points exist in collinear_facts
                    collinear_found = False
                    for fact in self.collinear_facts:
                        # Convert fact to normalized string for comparison
                        normalized_fact = self.normalize_collinear_points(''.join(fact))
                        if normalized_premise_points == normalized_fact:
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
                    angle1_points = self.normalize_angle_name(args[1])
                    angle2_points = self.normalize_angle_name(args[2])

                    # Get vertex of each normalized angle (middle point)
                    vertex1 = angle1_points[1]
                    vertex2 = angle2_points[1]

                    # Check if vertices are the same and both are in the normalized collinear points
                    if not (vertex1 == vertex2 and
                            all(p in normalized_premise_points for p in [vertex1, vertex2])):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Angles {args[1]} and {args[2]} must share a vertex on collinear line {points}",
                            details=f"After normalization: angles {angle1_points} and {angle2_points} on line {normalized_premise_points}"
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


        elif theorem_name == "similar_triangle_property_line_ratio":

            similar_match = re.search(r'SimilarBetweenTriangle\((\w+),(\w+)\)', premise)

            if not similar_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing similar triangles in premise",

                    details="similar_triangle_property_line_ratio requires similar triangles"

                ))

            tri1, tri2 = similar_match.groups()

            if not self.are_triangles_similar(tri1, tri2):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Triangles {tri1} and {tri2} are not proven similar",

                    details=f"Known similar triangles: {self.similar_triangles}"

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

            # Get all valid cyclic variations of both parallelograms

            theorem_variations = self.normalize_parallelogram(theorem_para)

            premise_variations = self.normalize_parallelogram(premise_para)

            # Check if there's any overlap between the variations

            if not (theorem_variations & premise_variations):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Theorem uses parallelogram {theorem_para} but premise specifies {premise_para}",

                    details=f"No matching cyclic variation found between theorem and premise parallelograms"

                ))

            # Also check if either parallelogram is defined in TEXT_CDL

            if not any(var in self.parallelograms for var in theorem_variations):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Parallelogram {theorem_para} is not defined in TEXT_CDL",

                    details=f"Available parallelograms: {', '.join(self.parallelograms)}"

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

            # Try all possible orientations of the lines

            possible_pairs = [

                (line1, line2),

                (line2, line1),

                (line1[::-1], line2),  # reversed first line

                (line1, line2[::-1]),  # reversed second line

                (line2[::-1], line1),  # both combinations reversed

                (line2, line1[::-1])

            ]

            if not any((pair in self.parallel_pairs or pair[::-1] in self.parallel_pairs) for pair in possible_pairs):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Lines {line1} and {line2} not proven parallel",

                    details=f"Available parallel pairs: {self.parallel_pairs}"

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
                            # Add all possible orientations
                            self.parallel_pairs.add((line1, line2))
                            self.parallel_pairs.add((line2, line1))
                            self.parallel_pairs.add((line1[::-1], line2))
                            self.parallel_pairs.add((line1, line2[::-1]))
                            print(f"Added parallel pairs: {line1} || {line2} and variations")
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
                    elif line.startswith('Collinear('):
                        points = line[10:-1]  # Extract points
                        normalized_points = self.normalize_collinear_points(points)
                        if normalized_points not in [''.join(fact) for fact in self.collinear_facts]:
                            self.collinear_facts.append(list(normalized_points))
                            self.add_collinear_fact(list(normalized_points))
                            print(f"Added normalized collinear points: {normalized_points}")

            # Parse goal and verify


            # Process CONSTRUCTION_CDL facts


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
                    elif line.startswith('Equal(LengthOfLine('):
                        # Add length values from TEXT_CDL
                        match = re.match(r'Equal\(LengthOfLine\((\w+)\),(\d+)\)', line)
                        if match:
                            line_name, value = match.group(1), float(match.group(2))
                            print(f"Found line length in TEXT_CDL: {line_name} = {value}")
                            normalized = self.normalize_line_name(line_name)
                            self.known_length_values[normalized] = value
                            # If we already have this length variable, add the constraint
                            if normalized in self.lengths:
                                self.solver.add(self.lengths[normalized] == value)
                    elif line.startswith('Parallelogram('):
                        match = re.match(r'Parallelogram\((\w+)\)', line)
                        if match:
                            para_name = match.group(1)
                            print(f"Found parallelogram in TEXT_CDL: {para_name}")
                            self.parallelograms.update(get_cyclic_variations(para_name))
                            print(f"Added parallelogram variations: {self.parallelograms}")
                    elif line.startswith('PerpendicularBetweenLine('):

                        match = re.match(r'PerpendicularBetweenLine\((\w+),\s*(\w+)\)', line)

                        if match:
                            line1, line2 = match.group(1), match.group(2)

                            print(f"Found perpendicular lines: {line1} ⊥ {line2}")

                            # Add both orientations to perpendicular pairs

                            self.perpendicular_pairs.add((line1, line2))

                            self.perpendicular_pairs.add((line2, line1))

                            # Find the shared vertex (common point between lines)

                            vertex = next(p for p in line1 if p in line2)

                            # Get the non-shared points from each line

                            first_point = next(p for p in line2 if p != vertex)  # From second line

                            last_point = next(p for p in line1 if p != vertex)  # From first line

                            # Create and normalize the 90° angle name: for BC⊥AC we get ACB = 90°

                            angle = f"{first_point}{vertex}{last_point}"

                            normalized_angle = self.normalize_angle_name(angle)

                            # Add the angle to both Z3 solver and known values

                            angle_var = self.add_angle(first_point, vertex, last_point)

                            self.solver.add(angle_var == 90)

                            self.known_angle_values[normalized_angle] = 90.0

                            print(f"Added 90° perpendicular angle constraint: {normalized_angle}")

                    elif line.startswith('SimilarBetweenTriangle('):
                        match = re.match(r'SimilarBetweenTriangle\((\w+),(\w+)\)', line)
                        if match:
                            tri1, tri2 = match.groups()
                            self.add_similar_triangles(tri1, tri2)



            print("\nCollected facts:")
            print("Collinear points:", self.collinear_facts)
            print("Parallel pairs:", self.parallel_pairs)
            print("Points:", list(self.points.keys()))

            # Process theorem sequence
            # Inside parse_and_verify_proof method
            # Process theorem sequence before verifying goal
            if 'THEOREM_SEQUENCE' in sections:
                sequence_text = '\n'.join(sections['THEOREM_SEQUENCE'])
                # Split into individual steps
                steps = [step.strip() for step in sequence_text.split('\n') if step.strip()]

                for step in steps:
                    # Split the step into its components using semicolon
                    parts = step.split(';')
                    if len(parts) >= 4:  # Should have step number, theorem call, premise, and conclusion
                        # Extract theorem name and arguments
                        theorem_part = parts[1].strip()
                        theorem_match = re.search(r'(\w+)\((.*?)\)', theorem_part)

                        if theorem_match:
                            theorem_name = theorem_match.group(1)
                            args = [arg.strip() for arg in theorem_match.group(2).split(',')]

                            # Get premise and conclusion
                            premise = parts[2].strip()
                            conclusions = eval(parts[3].strip())  # This will parse the list string

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

                # Try to match length goal first
                perimeter_match = re.search(r'Value\(PerimeterOfTriangle\((\w+)\)\)', goal_line)
                if perimeter_match:
                    triangle = perimeter_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected_answer = float(eval(sections['ANSWER'][0]))  # Use eval for fractions like "51/2"
                        print(f"\nGoal triangle perimeter: {triangle}")
                        print(f"Expected answer: {expected_answer}")

                        perimeter_var = self.calculate_perimeter(triangle)

                        # Check if solver is satisfiable with current constraints
                        if self.solver.check() == sat:
                            model = self.solver.model()
                            # Get the calculated value from the model
                            calculated_value = model.eval(perimeter_var).as_decimal(
                                10)  # Get as decimal with 10 digits precision
                            calculated_float = float(calculated_value)

                            # Compare with expected answer within small epsilon for floating point comparison
                            epsilon = 1e-10
                            if abs(calculated_float - expected_answer) < epsilon:
                                return True
                            else:
                                print(
                                    f"Error: Calculated value {calculated_float} does not match expected answer {expected_answer}")
                                return False
                        else:
                            print("Error: Constraints are unsatisfiable")
                            return False

                length_match = re.search(r'Value\(LengthOfLine\((\w+)\)\)', goal_line)
                if length_match:
                    goal_line = length_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected_answer = float(sections['ANSWER'][0])
                        print(f"\nGoal line: {goal_line}")
                        print(f"Expected answer: {expected_answer}")
                        # Only verify, don't add constraints
                        return self.verify_goal_length(goal_line[0], goal_line[1], expected_answer)

                # If not length, try angle goal
                angle_match = re.search(r'Value\(MeasureOfAngle\((\w+)\)\)', goal_line)
                if angle_match:
                    goal_angle = angle_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected_answer = float(sections['ANSWER'][0])
                        print(f"\nGoal angle: {goal_angle}")
                        print(f"Expected answer: {expected_answer}")
                        if self.algebraic_angles:
                            return self.verify_algebraic_goal(goal_angle, expected_answer)
                        else:
                            return self.verify_goal_angle(goal_angle[0], goal_angle[1], goal_angle[2], expected_answer)

                print("Error: Could not parse goal (neither angle nor length)")
                return False

            return True

        except Exception as e:

            print(f"Error during proof verification: {str(e)}")

            import traceback

            traceback.print_exc()

            return False

    def get_angle_value_helper_function_for_debuging(self, angle_name: str) -> Optional[float]:
        """Get the current value of an angle from the Z3 solver

        Args:
            angle_name: The name of the angle (e.g., 'ABC')

        Returns:
            Float value of the angle if it exists in the model, None otherwise
        """
        # First normalize the angle name
        normalized = self.normalize_angle_name(angle_name)

        # Check if we already know this angle's value
        if normalized in self.known_angle_values:
            return self.known_angle_values[normalized]

        # Get the angle variable from our angles dictionary
        angle_var = self.angles.get(f"angle_{normalized}")
        if angle_var is None:
            print(f"Angle {angle_name} not found in solver")
            return None

        # Check if solver is satisfiable
        if self.solver.check() == sat:
            model = self.solver.model()
            # Get value from model
            value = model.eval(angle_var)
            try:
                # Convert Z3 value to float
                float_val = float(str(value.as_decimal(10)))
                return float_val
            except:
                print(f"Could not convert angle value to float: {value}")
                return None
        else:
            print("Solver is unsatisfiable")
            return None


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
            "quadrilateral_property_angle_sum",
            "line_addition",  # Add this
            "right_triangle_judgment_angle",  # Add this
            "right_triangle_property_pythagorean",  # Add this,
            "similar_triangle_property_line_ratio",
            "triangle_perimeter_formula"
        ]

        if theorem_name not in valid_theorems:
            return GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL,
                message=f"Unknown theorem: {theorem_name}",
                details=f"Valid theorems are: {valid_theorems}"
            )

        if theorem_name == "parallelogram_property_opposite_angle_equal":
            angles_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),\s*MeasureOfAngle\((\w+)\)\)', conclusions[0])
            if angles_match:
                angle1, angle2 = angles_match.group(1), angles_match.group(2)

                # Add both angles to solver
                angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])
                self.solver.add(angle1_var == angle2_var)
                print(f"Added parallelogram opposite angle equality: {angle1} = {angle2}")

                # Add both original and reversed forms to relationships
                self.proven_angle_relationships.append(("equal", angle1, angle2))
                reversed_angle1 = angle1[2] + angle1[1] + angle1[0]  # BAD from DAB
                self.proven_angle_relationships.append(("equal", reversed_angle1, angle2))
                print(f"Added relationships: {angle1} = {angle2} and {reversed_angle1} = {angle2}")

                # If we know angle2's value, store it for both forms of angle1
                if angle2 in self.known_angle_values:
                    value = self.known_angle_values[angle2]
                    self.known_angle_values[angle1] = value
                    self.known_angle_values[reversed_angle1] = value
                    print(f"Proved angles {angle1} and {reversed_angle1} = {value} through parallelogram property")



        elif theorem_name == "similar_triangle_property_line_ratio":

            match = re.search(
                r'Equal\(LengthOfLine\((\w+)\),Mul\(LengthOfLine\((\w+)\),RatioOfSimilarTriangle\((\w+),(\w+)\)\)\)',
                conclusions[0])

            if match:

                line1, line2, tri1, tri2 = match.groups()

                # Get normalized triangle names to ensure consistent ratio variable

                norm_tris = self.normalize_similar_triangles(tri1, tri2)

                if not norm_tris:
                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message=f"Invalid triangle names: {tri1}, {tri2}"

                    )

                norm_tri1, norm_tri2 = norm_tris

                # Create or get ratio variable for these triangles

                ratio_key = (norm_tri1, norm_tri2)

                if ratio_key not in self.triangle_ratios:
                    self.triangle_ratios[ratio_key] = Real(f"ratio_{norm_tri1}_{norm_tri2}")

                ratio = self.triangle_ratios[ratio_key]

                # Add line ratio constraint

                line1_var = self.add_length(line1[0], line1[1])

                line2_var = self.add_length(line2[0], line2[1])

                self.solver.add(line1_var == line2_var * ratio)


        elif theorem_name == "triangle_perimeter_formula":

            match = re.search(
                r'Equal\(PerimeterOfTriangle\((\w+)\),Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)',
                conclusions[0])

            if match:
                triangle = match.group(1)

                side1 = match.group(2)

                side2 = match.group(3)

                side3 = match.group(4)

                # Create length variables for each side

                side1_var = self.add_length(side1[0], side1[1])

                side2_var = self.add_length(side2[0], side2[1])

                side3_var = self.add_length(side3[0], side3[1])

                # Calculate perimeter as sum of sides

                perimeter = side1_var + side2_var + side3_var

                # Store the perimeter expression

                self.triangle_perimeters[triangle] = perimeter

        elif theorem_name == "adjacent_complementary_angle":

            match = re.search(r'Equal\(Add\(MeasureOfAngle\((\w+)\),\s*MeasureOfAngle\((\w+)\)\),\s*180\)',
                              conclusions[0])

            if match:
                # Get angles and normalize them
                angle1, angle2 = match.group(1), match.group(2)
                norm_angle1 = self.normalize_angle_name(angle1)
                norm_angle2 = self.normalize_angle_name(angle2)

                # Add constraints using normalized angles
                angle1_var = self.add_angle(norm_angle1[0], norm_angle1[1], norm_angle1[2])
                angle2_var = self.add_angle(norm_angle2[0], norm_angle2[1], norm_angle2[2])
                self.solver.add(angle1_var + angle2_var == 180)

                print(f"Added supplementary angle constraint: {angle1} + {angle2} = 180")
                self.proven_angle_relationships.append(("supplementary", norm_angle1, norm_angle2))
                print(f"Added supplementary relationship: {norm_angle1} + {norm_angle2} = 180")

                # Handle known values using normalized angles
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


        elif theorem_name == "line_addition":
            lines_match = re.search(r'Equal\(LengthOfLine\((\w+)\),Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)', conclusions[0])
            if lines_match:
                total_line = lines_match.group(1)
                line1 = lines_match.group(2)
                line2 = lines_match.group(3)

                # Add length variables
                total_var = self.add_length(total_line[0], total_line[-1])
                line1_var = self.add_length(line1[0], line1[-1])
                line2_var = self.add_length(line2[0], line2[-1])

                # Add addition constraint
                self.solver.add(total_var == line1_var + line2_var)
                self.proven_length_relationships.append(("sum", line1, line2, total_line))


        elif theorem_name == "right_triangle_judgment_angle":

            # First check if polygon exists (Tier 1)

            polygon_match = re.search(r'Polygon\((\w+)\)', premise)

            if not polygon_match:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Missing polygon in premise",

                    details="right_triangle_judgment_angle requires a polygon"

                )

            triangle = polygon_match.group(1)

            if len(triangle) != 3:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message=f"Invalid triangle name: {triangle}",

                    details="Triangle must be specified by exactly 3 points"

                )

            # Check if angle exists and is 90° (Tier 2)

            angle_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),90\)', premise)
            if not angle_match:
                return GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing 90° angle in premise",
                    details="right_triangle_judgment_angle requires a 90° angle"
                )

            right_angle = angle_match.group(1)
            normalized_angle = self.normalize_angle_name(right_angle)  # Add this line

            # Change this condition to check normalized angle
            if (normalized_angle not in self.known_angle_values or
                    self.known_angle_values[normalized_angle] != 90):
                return GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Angle {right_angle} is not proven to be 90°",
                    details=f"Known angles: {self.known_angle_values}"
                )

            self.right_triangles.add(triangle)

            print(f"Added right triangle: {triangle}")

        elif theorem_name == "right_triangle_property_pythagorean":
            match = re.search(
                r'Equal\(Add\(Pow\(LengthOfLine\((\w+)\),2\),Pow\(LengthOfLine\((\w+)\),2\)\),Pow\(LengthOfLine\((\w+)\),2\)\)',
                conclusions[0])
            if match:
                leg1 = match.group(1)
                leg2 = match.group(2)
                hyp = match.group(3)

                # Add Pythagorean theorem constraint
                leg1_var = self.add_length(leg1[0], leg1[-1])
                leg2_var = self.add_length(leg2[0], leg2[-1])
                hyp_var = self.add_length(hyp[0], hyp[-1])

                self.solver.add(leg1_var * leg1_var + leg2_var * leg2_var == hyp_var * hyp_var)
                self.proven_length_relationships.append(("pythagorean", leg1, leg2, hyp))


        elif theorem_name == "parallel_property_alternate_interior_angle":
            angles_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),\s*MeasureOfAngle\((\w+)\)\)', conclusions[0])
            if angles_match:
                angle1, angle2 = angles_match.group(1), angles_match.group(2)

                # Add angles to solver
                angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])
                self.solver.add(angle1_var == angle2_var)
                print(f"Added parallel alternate angle equality: {angle1} = {angle2}")

                # Add to proven relationships
                self.proven_angle_relationships.append(("equal", angle1, angle2))
                print(f"Added relationship: {angle1} = {angle2}")

                # If we know one angle, store the other
                if angle1 in self.known_angle_values:
                    value = self.known_angle_values[angle1]
                    self.known_angle_values[angle2] = value
                    print(f"Proved angle {angle2} = {value} through parallel property")
                elif angle2 in self.known_angle_values:
                    value = self.known_angle_values[angle2]
                    self.known_angle_values[angle1] = value
                    print(f"Proved angle {angle1} = {value} through parallel property")

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


        elif theorem_name == "angle_addition":

            # Match the angle addition pattern from conclusions

            match = re.search(
                r'Equal\(MeasureOfAngle\((\w+)\),\s*Add\(MeasureOfAngle\((\w+)\),\s*MeasureOfAngle\((\w+)\)\)\)',
                conclusions[0])

            if match:

                sum_angle = match.group(1)  # ECB

                angle1 = match.group(2)  # ECD

                angle2 = match.group(3)  # DCB

                # Normalize all angles

                norm_sum = self.normalize_angle_name(sum_angle)

                norm_angle1 = self.normalize_angle_name(angle1)

                norm_angle2 = self.normalize_angle_name(angle2)

                # Add the constraint to the solver

                sum_var = self.add_angle(sum_angle[0], sum_angle[1], sum_angle[2])

                angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])

                angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                self.solver.add(sum_var == angle1_var + angle2_var)

                print(f"Added angle addition: {sum_angle} = {angle1} + {angle2}")

                # Track the proven relationship

                self.proven_angle_relationships.append(("sum", [angle1, angle2], sum_angle))

                print(f"Added sum relationship: {sum_angle} = {angle1} + {angle2}")

                # Check both original and normalized forms

                sum_value = None

                if sum_angle in self.known_angle_values:

                    sum_value = self.known_angle_values[sum_angle]

                elif norm_sum in self.known_angle_values:

                    sum_value = self.known_angle_values[norm_sum]

                angle2_value = None

                if angle2 in self.known_angle_values:

                    angle2_value = self.known_angle_values[angle2]

                elif norm_angle2 in self.known_angle_values:

                    angle2_value = self.known_angle_values[norm_angle2]

                # If we know both the sum and angle2, we can calculate angle1

                if sum_value is not None and angle2_value is not None:
                    angle1_value = sum_value - angle2_value

                    self.known_angle_values[angle1] = angle1_value

                    print(f"Proved angle {angle1} = {sum_value} - {angle2_value} = {angle1_value}")


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
    result = verify_geometric_proof(
        "/questions/the new format for questions after jan_17/new_7_questions/question_2425/question2425_v1")
    print(f"Verification {'succeeded' if result else 'failed'}")