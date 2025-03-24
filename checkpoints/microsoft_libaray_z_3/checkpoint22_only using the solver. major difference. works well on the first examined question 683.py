from z3 import *
import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple
from enum import Enum
from typing import Tuple, Optional
from fractions import Fraction



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

        # Solver and basic geometric elements
        self.solver = Solver()
        self.points = {}
        self.angles = {}
        self.parallel_pairs = set()
        self.perpendicular_pairs = set()
        self.collinear_facts = []

        # For handling both algebraic and numeric expressions
        self.variables = {}
        self.found_tier_1_or_2_error = False

        # Add these new attributes for length handling
        self.lengths = {}  # Store line lengths
        self.right_triangles = set()  # Add this line

        self.similar_triangles = []  # Store pairs of similar triangles
        self.triangle_perimeters = {}  # Store triangle perimeter values
        self.triangle_ratios = {}  # Store ratios between similar triangles
        self.added_ratio_constraints = set()

        self.polygons = set()
        self.squares = set()
        self.rectangles = set()
        self.rhombi = set()
        self.kites = set()

        self.circle_centers = {}  # e.g. circle_centers["D"] = "D" means point D is center of circle D
        self.circle_diameters = {}  # e.g. circle_diameters["D"] = "AB" means AB is the diameter of circle D
        self.circle_radii = {}  # store radius variable for circle, e.g. circle_radii["D"] = Real("radius_D")
        self.circle_areas = {}  # store area variable for circle, e.g. circle_areas["D"] = Real("area_D")

        # 2) We'll store any 'IsDiameterOfCircle(...)' statements here
        self.is_diameter_of_circle = []  # list of (line, circleName)

        # 3) We’ll also store any 'Cocircular(...)' facts, if needed
        self.cocircular_facts = []  # e.g. [("D", "B", "C", "A")] means D,B,C,A are on the same circle.

        # 4) For triangle area, we’ll keep a dictionary from triangle name to a Z3 Real for its area
        self.triangle_areas = {}

        # 5) We'll treat pi as a RealVal for approximate numeric checks
        self.pi_value = RealVal("3.141592653589793")  # Enough precision for typical geometry
        self.proven_area_relationships = []




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
        """Return the Z3 variable for the angle with vertex v formed by p1 and p2.
           All constraints are stored in the solver."""
        normalized = self.normalize_angle_name(p1 + v + p2)
        angle_name = f"angle_{normalized}"
        if angle_name not in self.angles:
            self.angles[angle_name] = Real(angle_name)
            # Constrain the angle to be between 0 and 180.
            self.solver.add(self.angles[angle_name] >= 0, self.angles[angle_name] <= 180)
        return self.angles[angle_name]

    def add_length(self, p1: str, p2: str) -> Real:
        """Return the Z3 variable for the length of the segment between p1 and p2.
           The variable is created if necessary and constrained to be nonnegative."""
        normalized = self.normalize_line_name(p1 + p2)
        length_name = f"length_{normalized}"
        if length_name not in self.lengths:
            self.lengths[length_name] = Real(length_name)
            # Add basic constraint: length >= 0.
            self.solver.add(self.lengths[length_name] >= 0)
        return self.lengths[length_name]



    def normalize_triangle(self, triangle: str) -> str:
        """Return the lexicographically smallest rotation of a triangle's name."""
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
        """Record that two triangles are similar and create their ratio variable.
           The order in which the triangles are given does not matter.
        """
        # Normalize each triangle independently.
        norm_tri1 = self.normalize_triangle(tri1)
        norm_tri2 = self.normalize_triangle(tri2)

        # Create a canonical (sorted) pair
        canonical_pair = (min(norm_tri1, norm_tri2), max(norm_tri1, norm_tri2))

        # Record the similarity (both orders are now equivalent)
        self.similar_triangles.append(canonical_pair)

        # Create a ratio variable if it does not already exist.
        if canonical_pair not in self.triangle_ratios:
            var_name = f"ratio_{canonical_pair[0]}_{canonical_pair[1]}"
            self.triangle_ratios[canonical_pair] = Real(var_name)
            print(f"Created ratio variable: {var_name}")

        # Optionally, add the side ratio constraints immediately.
        self.add_all_side_ratios_for_similar_triangles(tri1, tri2)

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

    def normalize_similar_triangles(self, tri1: str, tri2: str) -> Optional[Tuple[str, str]]:
        if len(tri1) != 3 or len(tri2) != 3:
            return None
        normalized = None
        for i in range(3):
            rot1 = tri1[i:] + tri1[:i]
            rot2 = tri2[i:] + tri2[:i]
            if normalized is None or (rot1, rot2) < normalized:
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



        # Given that 'points' is a list of collinear points in order (e.g. ['A', 'B', 'C'])
        if len(points) >= 3:
            # Process each endpoint of the collinear set
            for endpoint in (points[0], points[-1]):
                # Choose the neighbor that is adjacent to the endpoint:
                # – For the first endpoint, choose points[1]
                # – For the last endpoint, choose points[-2]
                ref = points[1] if endpoint == points[0] else points[-2]
                # For every other point in the collinear set (other than endpoint and its chosen neighbor)
                for other in points:
                    if other == endpoint or other == ref:
                        continue
                    # For every external point Q (i.e. a point not in the collinear set)
                    for q in self.points:
                        if q not in points:
                            # Construct the two angles:
                            # For the chosen (reference) angle at the endpoint, use the neighbor ref
                            angle_ref = self.normalize_angle_name(f"{ref}{endpoint}{q}")
                            # For the other candidate angle at the endpoint, use 'other'
                            angle_other = self.normalize_angle_name(f"{other}{endpoint}{q}")
                            # Add the equality constraint in the solver and record the relationship
                            a_ref_var = self.add_angle(angle_ref[0], angle_ref[1], angle_ref[2])
                            a_other_var = self.add_angle(angle_other[0], angle_other[1], angle_other[2])
                            self.solver.add(a_ref_var == a_other_var)
                            print(f"Derived from collinearity: {angle_ref} = {angle_other}")

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
            angle_var = self.add_angle(normalized[0], normalized[1], normalized[2])
            self.solver.add(angle_var == value)
            # Store the expression even though it's numeric
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


    def apply_triangle_area_sine(self):
        """
        For every stored triangle_area_sine relationship,
        if the solver can determine numeric values for both side lengths and the included angle,
        then compute the area and add a constraint fixing the area variable.
        """
        import math
        for rel in self.proven_area_relationships:
            if rel[0] == "triangle_area_sine":
                # rel is assumed to have the form:
                # ("triangle_area_sine", triangle_name, side1, side2, angle, factor_str)
                _, tri_name, s1, s2, ang, factor_str = rel

                # Get the Z3 variables for the two side lengths and the angle.
                s1_var = self.add_length(s1[0], s1[1])
                s2_var = self.add_length(s2[0], s2[1])
                ang_var = self.add_angle(ang[0], ang[1], ang[2])

                # Query the solver for numeric values.
                if self.solver.check() == sat:
                    model = self.solver.model()
                    try:
                        # Evaluate the side and angle variables.
                        val_s1 = model.eval(s1_var, model_completion=True)
                        val_s2 = model.eval(s2_var, model_completion=True)
                        val_ang = model.eval(ang_var, model_completion=True)
                        # Convert to float. (If the result ends with '?', remove it.)
                        s1_val = float(val_s1.as_decimal(10).rstrip('?'))
                        s2_val = float(val_s2.as_decimal(10).rstrip('?'))
                        ang_val = float(val_ang.as_decimal(10).rstrip('?'))
                    except Exception as e:
                        print("Could not convert model values to float:", e)
                        continue

                    try:
                        factor_val = float(eval(factor_str))
                    except Exception:
                        factor_val = 0.5

                    # Compute area numerically.
                    area_val = factor_val * s1_val * s2_val * math.sin(math.radians(ang_val))
                    # Create or get the triangle's area variable.
                    if tri_name not in self.triangle_areas:
                        self.triangle_areas[tri_name] = Real(f"areaTriangle_{tri_name}")
                        self.solver.add(self.triangle_areas[tri_name] >= 0)
                    self.solver.add(self.triangle_areas[tri_name] == area_val)
                    print(f"[apply_triangle_area_sine] Set AreaOfTriangle({tri_name}) = {area_val:.3f}")

    def verify_goal_length(self, p1: str, p2: str, expected: float, epsilon: float = 1e-10) -> bool:
        goal_line = p1 + p2
        normalized = self.normalize_line_name(goal_line)
        print(f"\nVerifying length goal: {normalized}")
        print(f"Expected value: {expected}")
        # Get the length variable.
        length_var = self.lengths.get(f"length_{normalized}")
        if length_var is None:
            print("Length variable not defined.")
            return False
        if self.solver.check() == sat:
            model = self.solver.model()
            calc_expr = model.eval(length_var, model_completion=True)
            val_str = calc_expr.as_decimal(10)
            if val_str.endswith('?'):
                val_str = val_str[:-1]
            # Handle any special strings.
            if val_str in ("oo", "+oo"):
                val_str = "inf"
            elif val_str == "-oo":
                val_str = "-inf"
            calculated_value = float(val_str)
            print(f"Calculated value for {normalized} is {calculated_value}")
            return abs(calculated_value - expected) < epsilon
        else:
            print("Solver constraints unsatisfiable when verifying length goal.")
            return False

    def triangle_angles(self, triangle: str) -> List[str]:
        """
        Returns the three canonical angle names (as strings) for the given triangle.
        For triangle "ADC", it returns the normalized versions of "DAC", "ADC", and "CDA".
        (Here the vertex is always the middle letter.)
        """
        angles = []
        # For each vertex index i in the triangle:
        for i in range(3):
            p_prev = triangle[(i - 1) % 3]
            vertex = triangle[i]
            p_next = triangle[(i + 1) % 3]
            angle_str = self.normalize_angle_name(p_prev + vertex + p_next)
            angles.append(angle_str)
        return angles

    def check_angle_equality(self, angle_str1: str, angle_str2: str) -> bool:
        """
        Returns True if, given the current constraints, the solver forces the angle variables
        corresponding to angle_str1 and angle_str2 to be equal.
        """
        # Get (or create) the angle variables.
        a1 = self.add_angle(angle_str1[0], angle_str1[1], angle_str1[2])
        a2 = self.add_angle(angle_str2[0], angle_str2[1], angle_str2[2])
        # Create a temporary solver that includes all current constraints.
        temp_solver = Solver()
        for c in self.solver.assertions():
            temp_solver.add(c)
        # Now add the extra constraint that a1 != a2.
        temp_solver.add(a1 != a2)
        # If that makes the system unsatisfiable, then a1 == a2 is forced.
        return temp_solver.check() == unsat

    def impose_square_constraints(self, shape_name: str):
        """
        Given a 4-letter shape name (like 'ABCD' or 'HEFG'),
        automatically impose the constraints for a square:
          - All 4 sides equal
          - All 4 interior angles are 90 degrees
        """
        # Make sure we have exactly 4 distinct letters
        if len(shape_name) != 4:
            return  # Skip if it's not 4 letters

        p1, p2, p3, p4 = shape_name[0], shape_name[1], shape_name[2], shape_name[3]

        # 1) Sides: AB=BC=CD=DA for shape ABCD
        side12 = self.add_length(p1, p2)
        side23 = self.add_length(p2, p3)
        side34 = self.add_length(p3, p4)
        side41 = self.add_length(p4, p1)
        # Impose equalities
        self.solver.add(side12 == side23)
        self.solver.add(side23 == side34)
        self.solver.add(side34 == side41)
        print(f"[Square {shape_name}] Imposed side equalities: {p1}{p2}={p2}{p3}={p3}{p4}={p4}{p1}")

        # 2) Angles: ABC=BCD=CDA=DAB=90
        # That means angle p1p2p3, angle p2p3p4, angle p3p4p1, angle p4p1p2 are each 90
        angle_123 = self.add_angle(p1, p2, p3)  # e.g. ABC
        angle_234 = self.add_angle(p2, p3, p4)  # e.g. BCD
        angle_341 = self.add_angle(p3, p4, p1)  # e.g. CDA
        angle_412 = self.add_angle(p4, p1, p2)  # e.g. DAB

        self.solver.add(angle_123 == 90)
        self.solver.add(angle_234 == 90)
        self.solver.add(angle_341 == 90)
        self.solver.add(angle_412 == 90)
        print(f"[Square {shape_name}] Imposed right angles at {p2}, {p3}, {p4}, {p1}")

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


        elif theorem_name == "diameter_of_circle_property_right_angle":
            # premise typically: IsDiameterOfCircle(BA,D)&Cocircular(DBCA)&Angle(BCA)
            # 1) Check IsDiameterOfCircle(BA,D) is among our is_diameter_of_circle
            # 2) Check Cocircular(DBCA) is in self.cocircular_facts
            # 3) Check 'Angle(BCA)' => just means that angle is recognized
            # If any fail -> Tier2 premise error

            # 1) check diameter premise
            diam_m = re.search(r'IsDiameterOfCircle\((\w+),(\w+)\)', premise)
            if not diam_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing or invalid IsDiameterOfCircle(...) in premise"
                ))
            line_name, circle_name = diam_m.groups()
            # see if (line_name, circle_name) is in self.is_diameter_of_circle
            if (line_name, circle_name) not in self.is_diameter_of_circle and (
            line_name[::-1], circle_name) not in self.is_diameter_of_circle:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Line {line_name} is not recorded as a diameter of circle {circle_name}"
                ))

            # 2) check Cocircular(...) e.g. Cocircular(DBCA)
            cocirc_m = re.search(r'Cocircular\((\w+)\)', premise)
            if not cocirc_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing Cocircular(...) in premise"
                ))
            points_str = cocirc_m.group(1)
            # e.g. 'DBCA'
            # Check if that set of points is in self.cocircular_facts
            # We can do a set comparison or just see if any tuple has the same chars
            # For simplicity, do this:
            found_cocirc = False
            for ctuple in self.cocircular_facts:
                if len(ctuple) == len(points_str):
                    if all(ch in ctuple for ch in points_str):
                        found_cocirc = True
                        break
            if not found_cocirc:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Cocircular({points_str}) was not established"
                ))

            # 3) check "Angle(BCA)" or similar
            angle_m = re.search(r'Angle\((\w+)\)', premise)
            if not angle_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing Angle(...) in premise"
                ))

            # If all good:
            return True, None

        elif theorem_name == "triangle_area_formula_sine":
            # premise example: Polygon(CAB)
            # conclusion: "Equal(AreaOfTriangle(CAB),Mul(LengthOfLine(CA),LengthOfLine(CB),Sin(MeasureOfAngle(ACB)),1/2))"
            # Just check premise has "Polygon(CAB)"
            pm = re.search(r'Polygon\((\w+)\)', premise)
            if not pm:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="triangle_area_formula_sine requires Polygon(...) in premise"
                ))
            # That’s enough for a basic Tier2 check
            return True, None

        elif theorem_name == "diameter_of_circle_property_length_equal":
            # premise: "IsDiameterOfCircle(BA,D)"
            # conclusion: "Equal(LengthOfLine(BA),DiameterOfCircle(D))"
            diam_m = re.search(r'IsDiameterOfCircle\((\w+),(\w+)\)', premise)
            if not diam_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing IsDiameterOfCircle(...) in premise"
                ))
            line_name, circle_name = diam_m.groups()
            if (line_name, circle_name) not in self.is_diameter_of_circle and (
            line_name[::-1], circle_name) not in self.is_diameter_of_circle:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Line {line_name} is not recorded as diameter of circle {circle_name}"
                ))
            return True, None

        elif theorem_name == "circle_property_length_of_radius_and_diameter":
            # premise: "Circle(D)"
            # conclusion: "Equal(DiameterOfCircle(D),Mul(RadiusOfCircle(D),2))"
            circ_m = re.search(r'Circle\((\w+)\)', premise)
            if not circ_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing Circle(...) in premise"
                ))
            circle_name = circ_m.group(1)
            if circle_name not in self.circle_radii:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Circle {circle_name} not known"
                ))
            return True, None

        elif theorem_name == "circle_area_formula":
            # premise: "Circle(D)"
            # conclusion: "Equal(AreaOfCircle(D),Mul(pi,RadiusOfCircle(D),RadiusOfCircle(D)))"
            circ_m = re.search(r'Circle\((\w+)\)', premise)
            if not circ_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing Circle(...) in premise for circle_area_formula"
                ))
            circle_name = circ_m.group(1)
            if circle_name not in self.circle_radii:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Circle {circle_name} is not declared"
                ))
            return True, None


        elif theorem_name == "square_property_definition":

            # We expect the premise to contain 'Square(ABCD)' or 'Square(HEFG)', etc.

            match = re.search(r'Square\((\w+)\)', premise)

            if not match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing Square(...) in premise",

                    details="square_property_definition theorem requires 'Square(XXXX)' in the premise"

                ))

            shape_name = match.group(1)

            # Now check if shape_name is recorded in self.squares

            if shape_name not in self.squares:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"{shape_name} not found in self.squares",

                    details=f"Found squares: {self.squares}"

                ))

            # If we get here, we accept the premise as valid

            return True, None



        elif theorem_name == "parallel_property_corresponding_angle":

            # Check the premise for "ParallelBetweenLine(...)" just like alt interior angles
            if "ParallelBetweenLine" not in premise:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing parallel lines in premise",
                    details="parallel_property_corresponding_angle theorem requires parallel lines"
                ))

            line_match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', premise)
            if not line_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Invalid parallel lines format in premise"
                ))

            line1, line2 = line_match.group(1), line_match.group(2)

            # Check we actually recorded them as parallel
            possible_pairs = [
                (line1, line2),
                (line2, line1),
                (line1[::-1], line2),
                (line1, line2[::-1]),
                (line2[::-1], line1),
                (line2, line1[::-1])
            ]

            if not any((pair in self.parallel_pairs or pair[::-1] in self.parallel_pairs)
                       for pair in possible_pairs):
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Lines {line1} and {line2} not proven parallel",
                    details=f"Available parallel pairs: {self.parallel_pairs}"
                ))

            # If you also want to require something like "Collinear(AED)" in the premise,
            # you can parse that, too. For instance:
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

            # If everything is good, return True
            return True, None



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






        elif theorem_name == "similar_triangle_judgment_aa":

            if len(args) < 3:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Insufficient arguments for similar_triangle_judgment_aa",
                    details="Expected similar_triangle_judgment_aa(1, triangle1, triangle2)"
                ))
            triangle1 = args[1].strip()  # e.g. "ADC"
            triangle2 = args[2].strip()  # e.g. "AEB"

            # First, check that these polygons exist in our stored polygons.
            norm_triangle1 = self.normalize_triangle(triangle1)
            norm_triangle2 = self.normalize_triangle(triangle2)
            if norm_triangle1 not in self.polygons:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Polygon for triangle {triangle1} is missing from the input data.",
                    details="The construction data did not define this polygon."
                ))
            if norm_triangle2 not in self.polygons:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Polygon for triangle {triangle2} is missing from the input data.",
                    details="The construction data did not define this polygon."
                ))
            # Next, check that the premise includes a polygon fact for each triangle.
            poly_matches = re.findall(r'Polygon\((\w+)\)', premise)
            if not any(triangle1 == poly or set(triangle1) == set(poly) for poly in poly_matches):
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Polygon for triangle {triangle1} is missing in the premise",
                    details="similar_triangle_judgment_aa requires a Polygon fact for the triangle"
                ))
            if not any(triangle2 == poly or set(triangle2) == set(poly) for poly in poly_matches):
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Polygon for triangle {triangle2} is missing in the premise",
                    details="similar_triangle_judgment_aa requires a Polygon fact for the triangle"
                ))
            # Now check that all angle equalities in the premise hold.
            # (For example, the premise may be:
            #  "Polygon(ADC)&Polygon(AEB)&Equal(MeasureOfAngle(ADC),MeasureOfAngle(AEB))&
            #   Equal(MeasureOfAngle(DCA),MeasureOfAngle(EBA))"
            # )
            # We split on '&' and for every clause that begins with "Equal(MeasureOfAngle(" we check the equality.
            conjuncts = [p.strip() for p in premise.split('&')]
            for conj in conjuncts:
                # If this conjunct is an angle equality, it should match the pattern:
                # Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))
                if conj.startswith("Equal(MeasureOfAngle("):
                    m = re.match(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conj)
                    if m:
                        ang1 = m.group(1)
                        ang2 = m.group(2)
                        # Use the solver to check that these two angles are forced equal.
                        if not self.check_angle_equality(ang1, ang2):
                            return return_error(GeometricError(
                                tier=ErrorTier.TIER2_PREMISE,
                                message=f"Premise angle equality {ang1} = {ang2} does not hold.",
                                details="The constraints do not force these two angles to be equal."
                            ))
                    else:
                        # If the pattern does not match, you might choose to ignore or return an error.
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Angle equality clause '{conj}' is not in the expected format.",
                            details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"
                        ))
            # If we got here, all parts of the premise are valid.
            return True, None




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

                    if line.startswith('Polygon('):
                        # Extract the polygon name; for instance, "ABC" from "Polygon(ABC)"
                        poly_match = re.match(r'Polygon\((\w+)\)', line)
                        if poly_match:
                            poly = poly_match.group(1)
                            # Normalize if you like (so that 'ABC' and 'BCA' are considered the same)
                            normalized_poly = self.normalize_triangle(poly) if len(poly) == 3 else poly
                            self.polygons.add(normalized_poly)
                            print(f"Added polygon: {normalized_poly}")

                    if line.startswith("Square("):
                        match = re.match(r"Square\((\w+)\)", line)
                        if match:
                            shape_name = match.group(1)
                            self.squares.add(shape_name)

                            # NEW LINE:
                            self.impose_square_constraints(shape_name)

                    elif line.startswith("Rectangle("):
                        match = re.match(r"Rectangle\((\w+)\)", line)
                        if match:
                            shape_name = match.group(1)
                            self.rectangles.add(shape_name)

                    elif line.startswith("Circle("):
                        # e.g. "Circle(D)" means we have a circle named D
                        circle_name = line[7:-1]  # get whatever is inside Circle(...)
                        # create radius, diameter, area Real variables if not already present
                        if circle_name not in self.circle_radii:
                            self.circle_radii[circle_name] = Real(f"radius_{circle_name}")
                            self.solver.add(self.circle_radii[circle_name] >= 0)
                        if circle_name not in self.circle_diameters:
                            # We'll store the diameter as another Z3 variable if needed
                            # but typically we only store "diameterOfCircle(D)" if a theorem sets it equal
                            pass
                        if circle_name not in self.circle_areas:
                            self.circle_areas[circle_name] = Real(f"area_{circle_name}")
                            self.solver.add(self.circle_areas[circle_name] >= 0)


                    elif line.startswith("Rhombus("):
                        match = re.match(r"Rhombus\((\w+)\)", line)
                        if match:
                            shape_name = match.group(1)
                            self.rhombi.add(shape_name)



                    elif line.startswith("Cocircular("):

                        # e.g. line = "Cocircular(D,BCA)"

                        # FIX: use [11:-1] instead of [10:-1]

                        inside = line[11:-1]  # This will be "D,BCA"

                        raw_fields = inside.split(',')

                        expanded_points = []

                        for token in raw_fields:

                            token = token.strip()

                            # If token length>1, expand each char individually

                            if len(token) > 1:

                                expanded_points.extend(list(token))

                            else:

                                expanded_points.append(token)

                        # Now store that as a tuple

                        self.cocircular_facts.append(tuple(expanded_points))

                        print(f"Added cocircular fact for points: {expanded_points}")



                    elif line.startswith("Kite("):
                        match = re.match(r"Kite\((\w+)\)", line)
                        if match:
                            shape_name = match.group(1)
                            self.kites.add(shape_name)

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
                print("\nProcessing CONSTRUCTION_CDL section...")
                for line in sections['CONSTRUCTION_CDL']:
                    print(f"Processing line: {line}")
                    if line.startswith('Collinear('):
                        points = line[10:-1]  # Extract points
                        normalized_points = self.normalize_collinear_points(points)
                        if normalized_points not in [''.join(fact) for fact in self.collinear_facts]:
                            self.collinear_facts.append(list(normalized_points))
                            self.add_collinear_fact(list(normalized_points))
                            print(f"Added normalized collinear points: {normalized_points}")


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
                        match = re.match(r'Equal\(LengthOfLine\((\w+)\),(.+)\)', line)
                        if match:
                            line_name, expression = match.groups()
                            expression = expression.strip()
                            print(f"Found length expression in TEXT_CDL: {line_name} = {expression}")
                            self.add_algebraic_length(line_name, expression)




                    elif line.startswith("IsCentreOfCircle("):
                        # e.g. "IsCentreOfCircle(D,D)" => means D is center of circle D
                        m = re.match(r'IsCentreOfCircle\((\w+),(\w+)\)', line)
                        if m:
                            point_name, circle_name = m.groups()
                            self.circle_centers[circle_name] = point_name

                    elif line.startswith("IsDiameterOfCircle("):
                        # e.g. "IsDiameterOfCircle(AB,D)"
                        m = re.match(r'IsDiameterOfCircle\((\w+),(\w+)\)', line)
                        if m:
                            line_name, circle_name = m.groups()
                            self.is_diameter_of_circle.append((line_name, circle_name))
                            # We will actually add constraints later, when the relevant theorems appear



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
                            error = self.adding_conclution(theorem_name, args, premise, conclusions)
                            if error:
                                print(f"\nError in {error.tier.name}:")
                                print(f"Message: {error.message}")
                                if error.details:
                                    print(f"Details: {error.details}")
                                return False

            if hasattr(self, 'proven_area_relationships'):
                self.apply_triangle_area_sine()

            if 'GOAL_CDL' in sections:
                goal_line = sections['GOAL_CDL'][0]

                # --- Check for a goal of the form:
                #     Value(Sub(AreaOfCircle(D),AreaOfTriangle(CAB)))
                sub_match = re.search(r'Value\(Sub\(AreaOfCircle\((\w+)\),AreaOfTriangle\((\w+)\)\)\)', goal_line)
                if sub_match:
                    circle_name, tri_name = sub_match.groups()
                    diff_var_name = f"diff_{circle_name}_{tri_name}"
                    diff_var = Real(diff_var_name)
                    self.solver.add(
                        diff_var >= 0)  # For example, assume the circle's area is at least the triangle's area

                    # Ensure the area variables exist (create them if not already present)
                    if circle_name not in self.circle_areas:
                        self.circle_areas[circle_name] = Real(f"area_{circle_name}")
                        self.solver.add(self.circle_areas[circle_name] >= 0)
                    if tri_name not in self.triangle_areas:
                        self.triangle_areas[tri_name] = Real(f"areaTriangle_{tri_name}")
                        self.solver.add(self.triangle_areas[tri_name] >= 0)

                    A_circle = self.circle_areas[circle_name]
                    A_tri = self.triangle_areas[tri_name]
                    self.solver.add(diff_var == A_circle - A_tri)

                    if 'ANSWER' in sections and sections['ANSWER']:
                        ans_str = sections['ANSWER'][0].strip()
                        # Replace 'pi' with its numeric approximation.
                        numeric_ans_expr = ans_str.replace('pi', '3.141592653589793')
                        try:
                            model_answer = float(eval(numeric_ans_expr))
                        except Exception as e:
                            print(f"Error parsing ANSWER expression: {e}")
                            return False

                        if self.solver.check() == sat:
                            model = self.solver.model()
                            val_in_model = model.eval(diff_var, model_completion=True)
                            val_str = val_in_model.as_decimal(10)
                            if val_str.endswith('?'):
                                val_str = val_str[:-1]
                            try:
                                calculated_value = float(val_str)
                            except ValueError:
                                print("Could not convert the difference to a float.")
                                return False

                            epsilon = 1e-7
                            if abs(calculated_value - model_answer) < epsilon:
                                print("Success: The difference matches the expected value.")
                                return True
                            else:
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message="The calculated difference does not match the expected value.",
                                    details=f"Calculated difference: {calculated_value}, Expected difference: {model_answer}."
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)
                                return False
                        else:
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message="The solver determined the goal is unsatisfiable.",
                                details=f"No valid solutions exist for AreaOfCircle({circle_name}) - AreaOfTriangle({tri_name})."
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)
                            return False
                    else:
                        print("No ANSWER provided; assuming goal is to establish the difference exists.")
                        return True

                # --- Check for a perimeter goal of the form:
                #     Value(PerimeterOfTriangle(ABC))
                perimeter_match = re.search(r'Value\(PerimeterOfTriangle\((\w+)\)\)', goal_line)
                if perimeter_match:
                    triangle = perimeter_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected_answer = float(eval(sections['ANSWER'][0].strip()))
                        print(f"\nGoal triangle perimeter: {triangle}")
                        print(f"Expected answer: {expected_answer}")

                        perimeter_var = self.calculate_perimeter(triangle)
                        if self.solver.check() == sat:
                            model = self.solver.model()
                            calculated_value_str = model.eval(perimeter_var).as_decimal(10)
                            if calculated_value_str.endswith('?'):
                                calculated_value_str = calculated_value_str[:-1]
                            try:
                                calculated_float = float(calculated_value_str)
                            except ValueError:
                                print("Could not convert the calculated perimeter to a float.")
                                return False

                            epsilon = 1e-10
                            if abs(calculated_float - expected_answer) < epsilon:
                                print("Success: The triangle perimeter matches the expected value.")
                                return True
                            else:
                                print(f"Error: Calculated perimeter {calculated_float} != expected {expected_answer}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message="Failed to prove triangle perimeter goal from the given theorems.",
                                    details=f"Goal was: PerimeterOfTriangle({triangle}) = {expected_answer}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)
                                return False
                        else:
                            print("Error: Constraints are unsatisfiable (solver.check() == unsat).")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message="Failed to prove perimeter goal: solver is unsatisfiable.",
                                details=f"Goal: PerimeterOfTriangle({triangle}) = {expected_answer}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)
                            return False

                # --- Check for a length goal of the form:
                #     Value(LengthOfLine(AB))
                length_match = re.search(r'Value\(LengthOfLine\((\w+)\)\)', goal_line)
                if length_match:
                    line_name = length_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        answer_str = sections['ANSWER'][0].strip()
                        try:
                            expected_answer = float(answer_str)
                        except ValueError:
                            from fractions import Fraction
                            expected_answer = float(Fraction(answer_str))
                        print(f"\nGoal line: {line_name}")
                        print(f"Expected answer: {expected_answer}")
                        verified = self.verify_goal_length(line_name[0], line_name[1], expected_answer)
                        if verified:
                            return True
                        else:
                            print(f"Error: Could not prove LengthOfLine({line_name}) = {expected_answer}")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message="Failed to prove length goal from the given theorems.",
                                details=f"Goal was: LengthOfLine({line_name}) = {expected_answer}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)
                            return False

                # --- Check for an angle goal of the form:
                #     Value(MeasureOfAngle(ABC))
                angle_match = re.search(r'Value\(MeasureOfAngle\((\w+)\)\)', goal_line)
                if angle_match:
                    goal_angle = angle_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        answer_str = sections['ANSWER'][0].strip()
                        try:
                            expected_answer = float(answer_str)
                        except ValueError:
                            from fractions import Fraction
                            expected_answer = float(Fraction(answer_str))
                        print(f"\nGoal angle: {goal_angle}")
                        print(f"Expected answer: {expected_answer}")
                        # Always use the direct measure check via verify_goal_angle:
                        success = self.verify_goal_angle(goal_angle[0], goal_angle[1], goal_angle[2], expected_answer)
                        if success:
                            return True
                        else:
                            print(f"Error: Could not prove MeasureOfAngle({goal_angle}) = {expected_answer}")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message="Failed to prove angle goal from the given theorems.",
                                details=f"Goal was: MeasureOfAngle({goal_angle}) = {expected_answer}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)
                            return False

                print("Error: Could not parse goal (neither angle, length, nor perimeter).")
                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message="Goal not recognized or not parsed properly",
                    details=f"Goal line content: {goal_line}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")
                if error.details:
                    print("Details:", error.details)
                return False


            return True

        except Exception as e:

            print(f"Error during proof verification: {str(e)}")

            import traceback

            traceback.print_exc()

            return False



    def verify_algebraic_goal(self, goal_angle: str, expected: float, epsilon: float = 1e-10) -> bool:
        print(f"\nVerifying goal angle: {goal_angle}")
        # Create or retrieve the angle variable.
        goal_var = self.add_angle(goal_angle[0], goal_angle[1], goal_angle[2])
        if self.solver.check() == sat:
            model = self.solver.model()
            val = model.eval(goal_var, model_completion=True)
            val_str = val.as_decimal(10)
            if val_str.endswith('?'):
                val_str = val_str[:-1]
            computed = float(val_str)
            print(f"Solver gives {goal_angle} = {computed}°")
            return abs(computed - expected) < epsilon
        else:
            print("Solver is unsat when evaluating goal angle.")
            return False



    def add_all_side_ratios_for_similar_triangles(self, tri1: str, tri2: str):
        # 1) Get the 3 vertices in order, e.g. tri1='BAE', tri2='CAD'
        def get_triangle_vertices(triangle_name: str) -> list:
            return list(triangle_name)

        verts1 = get_triangle_vertices(tri1)
        verts2 = get_triangle_vertices(tri2)

        # 2) Normalize the triangles and form a key
        norm_tris = self.normalize_similar_triangles(tri1, tri2)
        if not norm_tris:
            return  # Invalid triangles, do nothing

        # If we have already added constraints for this pair, return immediately.
        if norm_tris in self.added_ratio_constraints:
            return

        # Ensure a ratio variable exists:
        if norm_tris not in self.triangle_ratios:
            var_name = f"ratio_{norm_tris[0]}_{norm_tris[1]}"
            self.triangle_ratios[norm_tris] = Real(var_name)
        ratio = self.triangle_ratios[norm_tris]

        # 3) Add constraints for each corresponding side pair.
        for i in range(3):
            j = (i + 1) % 3
            p1a, p1b = verts1[i], verts1[j]
            p2a, p2b = verts2[i], verts2[j]
            side1_var = self.add_length(p1a, p1b)
            side2_var = self.add_length(p2a, p2b)
            self.solver.add(side1_var == side2_var * ratio)


        # Flag that we have now added the ratio constraints for this triangle pair.
        self.added_ratio_constraints.add(norm_tris)

    def add_algebraic_length(self, line_name: str, expression: str):
        """Add a length constraint that can be numeric or an algebraic expression."""
        print(f"\nAdding algebraic length constraint: {line_name} = {expression}")
        # First, try to parse the expression as a float.
        try:
            value = float(expression)
            print(f"Adding numeric value for line {line_name}: {value}")
            # Create (or get) the length variable.
            lvar = self.add_length(line_name[0], line_name[1])
            # Add the numeric constraint.
            self.solver.add(lvar == value)
            # Optionally, you could also store the numeric value (as you do with angles).
            return
        except ValueError:
            # Not a pure number, so we treat it as an algebraic expression.
            pass

        # Extract variables from the expression (if any)
        variables = self.extract_variables(expression)
        for var in variables:
            if var not in self.variables:
                self.variables[var] = Real(var)
                print(f"Created new variable for algebraic length: {var}")

        # Get (or create) the length variable.
        lvar = self.add_length(line_name[0], line_name[1])
        # Parse the expression using your algebraic parser.
        expr = self.parse_algebraic_expression(expression)
        # Add the constraint that the length variable equals the parsed expression.
        self.solver.add(lvar == expr)

    def adding_conclution(self, theorem_name: str, args: List[str], premise: str, conclusions: List[str]) -> \
    Optional[GeometricError]:
        print(f"\nProcessing theorem step: {theorem_name}")
        print(f"Arguments: {args}")
        print(f"Premise: '{premise}'")
        print(f"Conclusions: {conclusions}")

        valid_theorems = [
            "parallelogram_property_opposite_angle_equal",
            "adjacent_complementary_angle",
            "parallel_property_alternate_interior_angle",
            "parallel_property_corresponding_angle",
            "angle_addition",
            "quadrilateral_property_angle_sum",
            "line_addition",
            "right_triangle_judgment_angle",
            "right_triangle_property_pythagorean",
            "similar_triangle_property_line_ratio",
            "similar_triangle_judgment_aa",
            "triangle_perimeter_formula",
            "triangle_property_angle_sum",
            "square_property_definition",
            "diameter_of_circle_property_right_angle",
            "triangle_area_formula_sine",
            "diameter_of_circle_property_length_equal",
            "circle_property_length_of_radius_and_diameter",
            "circle_area_formula"
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
                norm_angle1 = self.normalize_angle_name(angle1)
                norm_angle2 = self.normalize_angle_name(angle2)
                reversed_angle1 = angle1[2] + angle1[1] + angle1[0]  # BAD from DAB
                print(f"Added relationships: {angle1} = {angle2} and {reversed_angle1} = {angle2}")



        elif theorem_name == "diameter_of_circle_property_right_angle":
            # conclusion is typically: ["PerpendicularBetweenLine(BC,AC)"]
            # So parse that: "PerpendicularBetweenLine(BC,AC)" => means angle BCA = 90
            conc = conclusions[0]
            m = re.match(r'PerpendicularBetweenLine\((\w+),(\w+)\)', conc)
            if m:
                line1, line2 = m.groups()
                # to impose perpendicular we do an angle of 90
                # e.g. if line1=BC, line2=AC, the shared point is C => angle BCA=90
                # Find the common letter. Usually the middle letter is the vertex
                vertex = None
                for p in line1:
                    if p in line2:
                        vertex = p
                        break
                if vertex is None or len(vertex) == 0:
                    # could raise an error, but let's just skip
                    return None
                # the other points are the endpoints
                # e.g. line1=BC => B or C is vertex, line2=AC => A or C is vertex
                # so angle is BCA or CBA or etc. We want the one that puts 'C' in the middle
                # we can do a quick check:
                other1 = [p for p in line1 if p != vertex][0]
                other2 = [p for p in line2 if p != vertex][0]
                angle_name = other1 + vertex + other2
                angle_name = self.normalize_angle_name(angle_name)
                angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])
                self.solver.add(angle_var == 90)
                print(f"diameter_of_circle_property_right_angle => set angle {angle_name} = 90")


        elif theorem_name == "triangle_area_formula_sine":

            # conclusion typically: ["Equal(AreaOfTriangle(CAB),Mul(LengthOfLine(CA),LengthOfLine(CB),Sin(MeasureOfAngle(ACB)),1/2))"]

            c = conclusions[0]

            pat = r"Equal\(AreaOfTriangle\((\w+)\),Mul\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),Sin\(MeasureOfAngle\((\w+)\)\),([\d/\.]+)\)\)"

            mm = re.match(pat, c)

            if mm:
                tri_name, side1, side2, angle_name, factor_str = mm.groups()

                # Just store the formula; we’ll do the numeric pinning later:

                self.proven_area_relationships.append((

                    "triangle_area_sine",

                    tri_name,

                    side1,

                    side2,

                    angle_name,

                    factor_str

                ))

                print(
                    f"[triangle_area_formula_sine] Stored: {tri_name} = {factor_str} * {side1} * {side2} * sin({angle_name})")


        elif theorem_name == "triangle_area_formula_sine":
            # conclusion: "Equal(AreaOfTriangle(CAB),Mul(LengthOfLine(CA),LengthOfLine(CB),Sin(MeasureOfAngle(ACB)),1/2))"
            c = conclusions[0]
            pattern = r"Equal\(AreaOfTriangle\((\w+)\),Mul\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),Sin\(MeasureOfAngle\((\w+)\)\),(.*?)\)\)"
            mm = re.match(pattern, c)
            if mm:
                tri, side1, side2, angle_str, factor_str = mm.groups()
                # We'll just store the relationship for a later numeric pass:
                self.proven_area_relationships.append(
                    ("triangle_area_sine", tri, side1, side2, angle_str, factor_str)
                )
                print(
                    f"[triangle_area_formula_sine] Stored relationship for {tri} = ½·{side1}·{side2}·sin({angle_str})")


        elif theorem_name == "diameter_of_circle_property_length_equal":
            # conclusion e.g.: "Equal(LengthOfLine(BA),DiameterOfCircle(D))"
            conc = conclusions[0]
            m = re.match(r'Equal\(LengthOfLine\((\w+)\),DiameterOfCircle\((\w+)\)\)', conc)
            if m:
                line_name, circle_name = m.groups()
                # create a Real for diameterOfCircle(D) if not exist
                diam_name = f"diameter_{circle_name}"
                if diam_name not in self.circle_diameters:
                    self.circle_diameters[diam_name] = Real(diam_name)
                    self.solver.add(self.circle_diameters[diam_name] >= 0)
                # get the line length
                ln_var = self.add_length(line_name[0], line_name[1])
                # set them equal
                self.solver.add(ln_var == self.circle_diameters[diam_name])
                print(f"diameter_of_circle_property_length_equal => {line_name} = diameter_{circle_name}")


        elif theorem_name == "circle_property_length_of_radius_and_diameter":
            # "Equal(DiameterOfCircle(D),Mul(RadiusOfCircle(D),2))"
            c = conclusions[0]
            mm = re.match(r'Equal\(DiameterOfCircle\((\w+)\),Mul\(RadiusOfCircle\((\w+)\),([\d/\.]+)\)\)', c)
            if mm:
                circle_diam, circle_rad, factor_str = mm.groups()
                # e.g. circle_diam=="D", circle_rad=="D", factor_str=="2"
                diam_name = f"diameter_{circle_diam}"
                rad_name = f"radius_{circle_rad}"
                if diam_name not in self.circle_diameters:
                    self.circle_diameters[diam_name] = Real(diam_name)
                    self.solver.add(self.circle_diameters[diam_name] >= 0)
                if circle_rad not in self.circle_radii:
                    self.circle_radii[circle_rad] = Real(rad_name)
                    self.solver.add(self.circle_radii[circle_rad] >= 0)
                factor_val = float(eval(factor_str))  # typically 2
                self.solver.add(self.circle_diameters[diam_name] == self.circle_radii[circle_rad] * factor_val)
                print(
                    f"circle_property_length_of_radius_and_diameter => diameter_{circle_diam} = 2 * radius_{circle_rad}")


        elif theorem_name == "circle_area_formula":
            # "Equal(AreaOfCircle(D),Mul(pi,RadiusOfCircle(D),RadiusOfCircle(D)))"
            c = conclusions[0]
            mm = re.match(r'Equal\(AreaOfCircle\((\w+)\),Mul\(pi,RadiusOfCircle\((\w+)\),RadiusOfCircle\(\2\)\)\)', c)
            # note \2 means same circle name in second capture
            if mm:
                circle_area, circle_rad = mm.groups()
                # create area Var if not exist
                if circle_area not in self.circle_areas:
                    self.circle_areas[circle_area] = Real(f"area_{circle_area}")
                    self.solver.add(self.circle_areas[circle_area] >= 0)
                # ensure radius var
                if circle_rad not in self.circle_radii:
                    self.circle_radii[circle_rad] = Real(f"radius_{circle_rad}")
                    self.solver.add(self.circle_radii[circle_rad] >= 0)

                # area(D) == pi * r(D)^2
                Avar = self.circle_areas[circle_area]
                Rvar = self.circle_radii[circle_rad]
                # This is a non‐linear constraint: A = pi_value * (R^2).
                self.solver.add(Avar == self.pi_value * (Rvar * Rvar))
                print(f"circle_area_formula => area_{circle_area} = pi * radius_{circle_rad}^2")



        elif theorem_name == "parallel_property_corresponding_angle":

            # Typically you'd expect the conclusion like "Equal(MeasureOfAngle(AEB),MeasureOfAngle(EDC))"

            angles_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),\s*MeasureOfAngle\((\w+)\)\)', conclusions[0])

            if angles_match:

                angle1, angle2 = angles_match.group(1), angles_match.group(2)

                # Normalize the angle names

                norm_angle1 = self.normalize_angle_name(angle1)

                norm_angle2 = self.normalize_angle_name(angle2)

                # Add them to the solver as angle variables

                angle1_var = self.add_angle(norm_angle1[0], norm_angle1[1], norm_angle1[2])

                angle2_var = self.add_angle(norm_angle2[0], norm_angle2[1], norm_angle2[2])

                # State they are equal

                self.solver.add(angle1_var == angle2_var)

                print(f"Added parallel corresponding angle equality: {norm_angle1} = {norm_angle2}")




        elif theorem_name == "square_property_definition":

            # Typically, the user’s THEOREM_SEQUENCE step might look like:

            #   square_property_definition(1,ABCD);

            #   Square(ABCD);

            #   ["Equal(LengthOfLine(AB),LengthOfLine(BC))",

            #    "Equal(LengthOfLine(BC),LengthOfLine(CD))",

            #    "Equal(LengthOfLine(CD),LengthOfLine(DA))",

            #    "Equal(MeasureOfAngle(ABC),90)",

            #    "Equal(MeasureOfAngle(BCD),90)",

            #    "Equal(MeasureOfAngle(CDA),90)",

            #    "Equal(MeasureOfAngle(DAB),90)"]

            for c in conclusions:

                # 1) Parse side-equality: "Equal(LengthOfLine(AB),LengthOfLine(BC))"

                m1 = re.match(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', c)

                if m1:
                    l1, l2 = m1.groups()

                    var1 = self.add_length(l1[0], l1[1])

                    var2 = self.add_length(l2[0], l2[1])

                    self.solver.add(var1 == var2)

                    print(f"Square property: {l1} == {l2}")

                    continue

                # 2) Parse angle = 90: "Equal(MeasureOfAngle(ABC),90)"

                m2 = re.match(r'Equal\(MeasureOfAngle\((\w+)\),(\d+)\)', c)

                if m2:
                    angle_name, deg_str = m2.groups()

                    deg_val = float(deg_str)

                    angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

                    self.solver.add(angle_var == deg_val)

                    print(f"Square property: angle {angle_name} == {deg_val}")

                    continue

                # etc. You can add other patterns if you want to unify sides with numbers, etc.

            return None

        elif theorem_name == "triangle_property_angle_sum":
            # Example premise: Polygon(DFC)
            # Example conclusion: ["Equal(Add(MeasureOfAngle(DFC),MeasureOfAngle(FCD),MeasureOfAngle(CDF)),180)"]

            # 1) Check that premise has Polygon(???). Typically: "Polygon(DFC)"
            poly_match = re.search(r'Polygon\((\w+)\)', premise)
            if not poly_match:
                return GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing or invalid Polygon() in premise for triangle_property_angle_sum"
                )
            triangle_points = poly_match.group(1)

            # 2) In your conclusion, look for that typical pattern:
            #    "Equal(Add(MeasureOfAngle(DFC),MeasureOfAngle(FCD),MeasureOfAngle(CDF)),180)"
            match = re.search(
                r'Equal\(Add\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\),180\)',
                conclusions[0]
            )
            if match:
                a1, a2, a3 = match.groups()

                # Add angle vars in the solver:
                angle1_var = self.add_angle(a1[0], a1[1], a1[2])
                angle2_var = self.add_angle(a2[0], a2[1], a2[2])
                angle3_var = self.add_angle(a3[0], a3[1], a3[2])

                # Add sum constraint: angle1 + angle2 + angle3 = 180
                self.solver.add(angle1_var + angle2_var + angle3_var == 180)


            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Conclusion format error for triangle_property_angle_sum",
                    details=f"Expected 3-angle sum = 180, got {conclusions[0]}"
                )

        elif theorem_name == "similar_triangle_judgment_aa":
            # Expect a conclusion like ["SimilarBetweenTriangle(BAE,CAD)"]
            match = re.search(r'SimilarBetweenTriangle\((\w+),(\w+)\)', conclusions[0])
            if match:
                tri1, tri2 = match.groups()
                print(f"Adding that triangles {tri1} and {tri2} are similar by AA.")
                self.add_similar_triangles(tri1, tri2)
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Conclusion format error for similar_triangle_judgment_aa",
                    details=f"Expected SimilarBetweenTriangle(...) but got {conclusions[0]}"
                )


        elif theorem_name == "similar_triangle_property_line_ratio":

            match = re.search(

                r'Equal\(LengthOfLine\((\w+)\),'

                r'Mul\(LengthOfLine\((\w+)\),'

                r'RatioOfSimilarTriangle\((\w+),(\w+)\)\)\)',

                conclusions[0]

            )

            if match:

                line1, line2, tri1, tri2 = match.groups()

                norm_tris = self.normalize_similar_triangles(tri1, tri2)

                if not norm_tris:
                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message=f"Invalid triangle names: {tri1}, {tri2}"

                    )

                # Look up the ratio variable.

                if norm_tris not in self.triangle_ratios:
                    var_name = f"ratio_{norm_tris[0]}_{norm_tris[1]}"

                    self.triangle_ratios[norm_tris] = Real(var_name)

                ratio = self.triangle_ratios[norm_tris]

                line1_var = self.add_length(line1[0], line1[1])

                line2_var = self.add_length(line2[0], line2[1])

                self.solver.add(line1_var == line2_var * ratio)

                # (Optionally, call add_all_side_ratios_for_similar_triangles if not added yet;

                #  however, our flag in added_ratio_constraints should prevent duplicates.)

                self.add_all_side_ratios_for_similar_triangles(tri1, tri2)

                print(f"Added ratio constraints for all corresponding sides of {tri1} and {tri2}.")


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


                print(f"Added supplementary relationship: {norm_angle1} + {norm_angle2} = 180")




        elif theorem_name == "line_addition":

            match = re.search(

                r'Equal\(LengthOfLine\((\w+)\),Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)',

                conclusions[0]

            )

            if match:
                total, part1, part2 = match.group(1), match.group(2), match.group(3)

                # Get (or create) the Z3 variables for each segment.

                total_var = self.add_length(total[0], total[1])

                part1_var = self.add_length(part1[0], part1[1])

                part2_var = self.add_length(part2[0], part2[1])

                # Add the addition constraint and basic nonnegative constraints.

                self.solver.add(total_var == part1_var + part2_var,

                                part1_var > 0, part2_var > 0, total_var > 0)




        elif theorem_name == "right_triangle_property_pythagorean":

            match = re.search(

                r'Equal\(Add\(Pow\(LengthOfLine\((\w+)\),2\),Pow\(LengthOfLine\((\w+)\),2\)\),Pow\(LengthOfLine\((\w+)\),2\)\)',

                conclusions[0]

            )

            if match:
                leg1, leg2, hyp = match.group(1), match.group(2), match.group(3)

                # Create or retrieve the side variables.

                leg1_var = self.add_length(leg1[0], leg1[1])

                leg2_var = self.add_length(leg2[0], leg2[1])

                hyp_var = self.add_length(hyp[0], hyp[1])

                # Constrain them to be positive.

                self.solver.add(leg1_var > 0, leg2_var > 0, hyp_var > 0)

                # Add the Pythagorean constraint.

                self.solver.add(leg1_var * leg1_var + leg2_var * leg2_var == hyp_var * hyp_var)

                # (If any known value was provided in TEXT_CDL, the corresponding constraint would have already been added.)

                # Add extra ordering constraints.

                self.solver.add(leg1_var + leg2_var > hyp_var)

                self.solver.add(hyp_var > leg1_var, hyp_var > leg2_var)




        elif theorem_name == "parallel_property_alternate_interior_angle":
            m = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conclusions[0])
            if m:
                angle1, angle2 = m.group(1), m.group(2)
                a1 = self.add_angle(angle1[0], angle1[1], angle1[2])
                a2 = self.add_angle(angle2[0], angle2[1], angle2[2])
                self.solver.add(a1 == a2)
                print(f"Added constraint: {angle1} == {angle2}")
            else:
                return GeometricError(tier=ErrorTier.TIER1_THEOREM_CALL,
                                      message="Conclusion format error for parallel_property_alternate_interior_angle",
                                      details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))")


        elif theorem_name == "quadrilateral_property_angle_sum":

            if len(args) < 2:
                return GeometricError(tier=ErrorTier.TIER1_THEOREM_CALL,

                                      message="Invalid number of arguments",

                                      details="Expected quadrilateral name")

            quad_name = args[1]

            angle_vars = []

            for i in range(len(quad_name)):
                p1 = quad_name[i]

                p2 = quad_name[(i + 1) % len(quad_name)]

                p3 = quad_name[(i + 2) % len(quad_name)]

                avar = self.add_angle(p1, p2, p3)

                angle_vars.append(avar)

                print(f"Angle at vertex {p2} added for quadrilateral {quad_name}")

            self.solver.add(sum(angle_vars) == 360)

            print("Added quadrilateral angle sum constraint: sum of angles = 360°")



        elif theorem_name == "angle_addition":

            m = re.search(
                r'Equal\(MeasureOfAngle\((\w{3})\),\s*Add\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)\)',
                conclusions[0])

            if m:

                sum_angle, angle1, angle2 = m.group(1), m.group(2), m.group(3)

                sum_var = self.add_angle(sum_angle[0], sum_angle[1], sum_angle[2])

                angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])

                angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                self.solver.add(sum_var == angle1_var + angle2_var)

                print(f"Added angle addition constraint: {sum_angle} = {angle1} + {angle2}")

            else:

                return GeometricError(tier=ErrorTier.TIER1_THEOREM_CALL,

                                      message="Conclusion format error for angle_addition",

                                      details="Expected format: Equal(MeasureOfAngle(XXX),Add(MeasureOfAngle(YYY),MeasureOfAngle(ZZZ)))")

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
        "/questions/the new format for questions after jan_17/new_7_questions/question_729_problem_in_the_order_of_simillarity_in_normal_gt/question729_gt")
    print(f"Verification {'succeeded' if result else 'failed'}")