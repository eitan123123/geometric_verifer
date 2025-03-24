from z3 import *
import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple
from enum import Enum
from typing import Tuple, Optional
from fractions import Fraction
import logging


class ErrorTier(Enum):
    TIER1_THEOREM_CALL = 1  # Incorrect theorem call
    TIER2_PREMISE = 2  # Premise violation
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
        self.pi = Real('pi')
        self.solver.add(self.pi == 3.141592653589793)
        self.points = {}
        self.angles = {}
        self.parallel_pairs = set()
        self.perpendicular_pairs = set()
        self.collinear_facts = []
        self.theorem_sequence = []
        self.question_name = "unknown_question"


        self.altitude_facts = set()
        self.trapezoids = set()
        self.altitudes = {}
        self.quad_areas = {}
        self.quad_heights = {}

        # For handling both algebraic and numeric expressions
        self.variables = {}
        self.found_tier_1_or_2_error = False


        self.quadrilateral_diagonals = set()
        self.quadrilateral_right_angles = set()


        # Add these new attributes for length handling
        self.lengths = {}  # Store line lengths
        self.right_triangles = set()  # Add this line

        self.arcs = {}
        self.similar_triangles = []  # Store pairs of similar triangles
        self.triangle_perimeters = {}  # Store triangle perimeter values
        self.triangle_ratios = {}  # Store ratios between similar triangles
        self.added_ratio_constraints = set()

        self.mirror_similar_triangles = []  # List of canonical pairs proven mirror similar
        self.mirror_triangle_ratios = {}  # Map canonical pair -> Z3 Real variable for mirror ratio
        self.added_mirror_ratio_constraints = set()

        self.polygons = set()
        self.squares = set()
        self.rectangles = set()
        self.rhombi = set()
        self.kites = set()

        self.circle_centers = {}  # e.g. circle_centers["D"] = "D" means point D is center of circle D
        self.circle_diameters = {}  # e.g. circle_diameters["D"] = "AB" means AB is the diameter of circle D
        self.circle_radii = {}  # store radius variable for circle, e.g. circle_radii["D"] = Real("radius_D")
        self.circle_areas = {}  # store area variable for circle, e.g. circle_areas["D"] = Real("area_D")
        self.tangent_facts = set()  # e.g. set of tuples like ("AN", "O")
        self.cocircular_facts = []  # e.g. list of tuples like ("O", "B", "M")

        # 2) We'll store any 'IsDiameterOfCircle(...)' statements here
        self.is_diameter_of_circle = []  # list of (line, circleName)

        # 3) We’ll also store any 'Cocircular(...)' facts, if needed
        self.cocircular_facts = []  # e.g. [("D", "B", "C", "A")] means D,B,C,A are on the same circle.

        # 4) For triangle area, we’ll keep a dictionary from triangle name to a Z3 Real for its area
        self.triangle_areas = {}

        # 5) We'll treat pi as a RealVal for approximate numeric checks
        from z3 import Const, RealVal, RealSort

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

    def canonicalize_mirror_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Normalize each triangle by sorting its vertices alphabetically, then
        return a tuple of the two normalized names sorted in alphabetical order.
        For example, if tri1 = "EGH" and tri2 = "FEG":
          - "EGH" stays "EGH" (if already sorted)
          - "FEG" becomes "EFG"
          - Then the tuple is sorted to yield ("EFG", "EGH")
        """
        tri1_norm = ''.join(sorted(tri1.strip().upper()))
        tri2_norm = ''.join(sorted(tri2.strip().upper()))
        return tuple(sorted([tri1_norm, tri2_norm]))

    def add_mirror_similar_triangles(self, tri1: str, tri2: str):
        """Record that triangles tri1 and tri2 are mirror similar (by AA)
        and create a corresponding ratio variable if not already defined."""
        canonical_pair = self.canonicalize_mirror_triangle_pair(tri1, tri2)

        if canonical_pair not in self.mirror_similar_triangles:
            self.mirror_similar_triangles.append(canonical_pair)
            print(f"Recorded mirror similarity for triangles: {canonical_pair}")
        if canonical_pair not in self.mirror_triangle_ratios:
            var_name = f"ratio_mirror_{canonical_pair[0]}_{canonical_pair[1]}"
            self.mirror_triangle_ratios[canonical_pair] = Real(var_name)
            print(f"Created mirror similar ratio variable: {var_name}")
        # self.add_all_side_mirror_ratio_constraints(tri1, tri2)

    def add_all_side_mirror_ratio_constraints(self, tri1: str, tri2: str):
        """For mirror similar triangles, add side‐ratio constraints for each corresponding side.
        (This is analogous to add_all_side_ratios_for_similar_triangles.)"""

        def get_triangle_vertices(triangle_name: str) -> list:
            return list(triangle_name)

        verts1 = get_triangle_vertices(tri1)
        verts2 = get_triangle_vertices(tri2)
        norm_tris = self.normalize_similar_triangles(tri1, tri2)
        if not norm_tris:
            return
        if norm_tris in self.added_mirror_ratio_constraints:
            return
        if norm_tris not in self.mirror_triangle_ratios:
            var_name = f"ratio_mirror_{norm_tris[0]}_{norm_tris[1]}"
            self.mirror_triangle_ratios[norm_tris] = Real(var_name)
        ratio = self.mirror_triangle_ratios[norm_tris]
        for i in range(3):
            j = (i + 1) % 3
            p1a, p1b = verts1[i], verts1[j]
            p2a, p2b = verts2[i], verts2[j]
            side1_var = self.add_length(p1a, p1b)
            side2_var = self.add_length(p2a, p2b)
            self.solver.add(side1_var == side2_var * ratio)
        self.added_mirror_ratio_constraints.add(norm_tris)
        print(f"Added mirror similar side ratio constraints for triangles {tri1} and {tri2}.")

    def normalize_triangle(self, triangle: str) -> str:
        """Return the lexicographically smallest rotation of a triangle's name."""
        if len(triangle) != 3:
            return triangle
        rotations = [triangle[i:] + triangle[:i] for i in range(3)]
        return min(rotations)

    def are_triangles_similar(self, tri1: str, tri2: str) -> bool:
        # Use mirror–similar canonicalization for the purpose of mirror similarity
        canonical = self.canonicalize_mirror_triangle_pair(tri1, tri2)
        return canonical in self.similar_triangles or (canonical[1], canonical[0]) in self.similar_triangles

    def canonicalize_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Given two triangles (each represented by a 3‐letter string),
        compute a canonical key that is invariant under (a) cyclic rotations (applied in lock‐step)
        and (b) switching the order of the triangles.

        For each rotation index i (0, 1, 2), we compute:
            r1 = tri1 rotated by i, and r2 = tri2 rotated by i.
        Then we consider both (r1, r2) and (r2, r1) (to be order–invariant)
        and choose the lexicographically smallest pair. Finally, we pick the smallest candidate
        among the three rotations.
        """
        if len(tri1) != 3 or len(tri2) != 3:
            raise ValueError("Each triangle must have exactly 3 vertices.")

        candidates = []
        for i in range(3):
            r1 = tri1[i:] + tri1[:i]
            r2 = tri2[i:] + tri2[:i]
            # Preserve the lock‐step rotation by first forming the candidate (r1, r2),
            # but then to get order invariance, compare with the swapped order.
            candidate = min((r1, r2), (r2, r1))
            candidates.append(candidate)

        return min(candidates)

    def canonicalize_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Given two triangles (each represented by a 3‐letter string),
        compute a canonical key that is invariant under (a) cyclic rotations (applied in lock‐step)
        and (b) switching the order of the triangles.

        For each rotation index i (0, 1, 2), we compute:
            r1 = tri1 rotated by i, and r2 = tri2 rotated by i.
        Then we consider both (r1, r2) and (r2, r1) (to be order–invariant)
        and choose the lexicographically smallest pair. Finally, we pick the smallest candidate
        among the three rotations.
        """
        if len(tri1) != 3 or len(tri2) != 3:
            raise ValueError("Each triangle must have exactly 3 vertices.")

        candidates = []
        for i in range(3):
            r1 = tri1[i:] + tri1[:i]
            r2 = tri2[i:] + tri2[:i]
            # Preserve the lock‐step rotation by first forming the candidate (r1, r2),
            # but then to get order invariance, compare with the swapped order.
            candidate = min((r1, r2), (r2, r1))
            candidates.append(candidate)

        return min(candidates)

    def canonicalize_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Given two triangles (each represented by a 3‐letter string),
        compute a canonical key that is invariant under (a) cyclic rotations (applied in lock‐step)
        and (b) switching the order of the triangles.

        For each rotation index i (0, 1, 2), we compute:
            r1 = tri1 rotated by i, and r2 = tri2 rotated by i.
        Then we consider both (r1, r2) and (r2, r1) (to be order–invariant)
        and choose the lexicographically smallest pair. Finally, we pick the smallest candidate
        among the three rotations.
        """
        if len(tri1) != 3 or len(tri2) != 3:
            raise ValueError("Each triangle must have exactly 3 vertices.")

        candidates = []
        for i in range(3):
            r1 = tri1[i:] + tri1[:i]
            r2 = tri2[i:] + tri2[:i]
            # Preserve the lock‐step rotation by first forming the candidate (r1, r2),
            # but then to get order invariance, compare with the swapped order.
            candidate = min((r1, r2), (r2, r1))
            candidates.append(candidate)

        return min(candidates)

    def add_similar_triangles(self, tri1: str, tri2: str):
        """
        Record that two triangles are similar and create their ratio variable.
        This function uses a canonical key obtained from cyclic rotations so that
        the pair (tri1, tri2) is uniquely identified regardless of rotation or order.
        """
        # Get the canonical pair from our helper.
        canonical_pair = self.canonicalize_mirror_triangle_pair(tri1, tri2)


        # Record the similarity using the canonical pair.
        self.similar_triangles.append(canonical_pair)

        # Create a ratio variable if it does not already exist.
        if canonical_pair not in self.triangle_ratios:
            var_name = f"ratio_{canonical_pair[0]}_{canonical_pair[1]}"
            self.triangle_ratios[canonical_pair] = Real(var_name)
            print(f"Created ratio variable: {var_name}")

        # Optionally, add the side ratio constraints immediately.


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
        triangle = self.normalize_triangle(points)
        self.right_triangles.add(triangle)

        # Add 90° angle constraint
        angle_var = self.add_angle(points[0], points[1], points[2])


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

    def normalize_arc(self, arc_str: str) -> str:
        """
        Normalize an arc name. For an arc given by three letters,
        the first character (the center) is kept in place,
        and the remaining two letters (the endpoints) are sorted alphabetically.
        For example, both "OMB" and "OBM" become "OBM".
        """
        if len(arc_str) != 3:
            return arc_str
        center = arc_str[0]
        endpoints = sorted([arc_str[1], arc_str[2]])
        return center + ''.join(endpoints)

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

    def add_algebraic_arc(self, arc_name: str, expression: str):
        """Add an arc measure constraint that can be numeric or an algebraic expression."""
        print(f"\nAdding algebraic arc constraint: {arc_name} = {expression}")
        # Try to parse as a numeric value first.
        try:
            value = float(expression)
            print(f"Adding numeric value for arc {arc_name}: {value}")
            arc_var = self.add_arc(arc_name)
            self.solver.add(arc_var == value)
            return
        except ValueError:
            pass
        # If not purely numeric, extract any variables and create them if necessary.
        variables = self.extract_variables(expression)
        for var in variables:
            if var not in self.variables:
                self.variables[var] = Real(var)
                print(f"Created new variable for algebraic arc: {var}")
        arc_var = self.add_arc(arc_name)
        expr = self.parse_algebraic_expression(expression)
        self.solver.add(arc_var == expr)

    def add_arc(self, arc_str: str) -> Real:
        """
        Return the Z3 variable for the measure of the arc given by arc_str.
        The arc is normalized so that its first letter (the center) is fixed
        and the other two letters are sorted. We then constrain the arc measure
        to be between 0 and 360 (you can adjust the range as needed).
        """
        normalized = self.normalize_arc(arc_str)
        arc_name = f"arc_{normalized}"
        if arc_name not in self.arcs:
            self.arcs[arc_name] = Real(arc_name)
            self.solver.add(self.arcs[arc_name] >= 0, self.arcs[arc_name] <= 360)
            print(f"Created arc variable: {arc_name}")
        return self.arcs[arc_name]

    def add_collinear_fact(self, points: List[str]):
        """Add collinear points fact with supplementary angle relationships"""
        if len(points) < 3:
            return

        # Join points to string and normalize
        points_str = ''.join(points)
        normalized = self.normalize_collinear_points(points_str)
        points = list(normalized)  # Convert back to list

        # Also create reversed points
        reversed_points = points[::-1]

        # Process both orders
        for point_order in [points, reversed_points]:
            # For each three consecutive points
            for i in range(len(point_order) - 2):
                p1, v, p2 = point_order[i:i + 3]

                # Add points if they don't exist
                for p in [p1, v, p2]:
                    if p not in self.points:
                        self.add_point(p)

                # Add straight angle constraint (180°) - use normalized angle
                straight_angle = self.normalize_angle_name(p1 + v + p2)
                angle_var = self.add_angle(straight_angle[0], straight_angle[1], straight_angle[2])

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
                        # Each angle must be between 0° and 180°
                        self.solver.add(angle1_var > 0)
                        self.solver.add(angle1_var < 180)
                        self.solver.add(angle2_var > 0)
                        self.solver.add(angle2_var < 180)

            # Process endpoints for this order
            if len(point_order) >= 3:
                # Process each endpoint of the collinear set
                for endpoint in (point_order[0], point_order[-1]):
                    # Choose the neighbor that is adjacent to the endpoint
                    ref = point_order[1] if endpoint == point_order[0] else point_order[-2]

                    # For every other point in the collinear set
                    for other in point_order:
                        if other == endpoint or other == ref:
                            continue

                        # For every external point Q
                        for q in self.points:
                            if q not in point_order:
                                # Construct the angles
                                angle_ref = self.normalize_angle_name(f"{ref}{endpoint}{q}")
                                angle_other = self.normalize_angle_name(f"{other}{endpoint}{q}")

                                # Add the equality constraint
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

            # Try to convert to float first with math functions
            try:
                import math
                eval_env = {"sqrt": math.sqrt, "pi": math.pi}
                return float(eval(expr, {"__builtins__": {}}, eval_env))
            except Exception:
                pass

            # Check for sqrt pattern
            sqrt_match = re.search(r'sqrt\((.+?)\)', expr)
            if sqrt_match:
                inner_expr = sqrt_match.group(1)
                inner_value = self.parse_algebraic_expression(inner_expr)
                # Use z3's power function for square root
                from z3 import Pow
                return Pow(inner_value, 0.5)

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
                left, right = expr.split('*', 1)  # Changed to split on first '*'
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
                        val_s1 = model.eval(s1_var)
                        val_s2 = model.eval(s2_var)
                        val_ang = model.eval(ang_var)
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

    def verify_goal_arc(self, arc_name: str, expected: float, epsilon: float = 1e-8) -> bool:
        goal_arc = arc_name  # For arcs, we can assume the naming is like "BVT" or "BSU"
        print(f"\nVerifying arc goal: {goal_arc}")
        arc_var = self.arcs.get(f"arc_{self.normalize_arc(arc_name)}")
        if arc_var is None:
            print("Arc variable not defined.")
            return False

        if self.solver.check() == sat:
            # First check if constraints allow the expected value
            temp_solver1 = Solver()
            for c in self.solver.assertions():
                temp_solver1.add(c)

            # Add constraint that arc_var == expected (within epsilon)
            temp_solver1.add(And(arc_var >= expected - epsilon, arc_var <= expected + epsilon))

            if temp_solver1.check() != sat:
                print(f"Error: Constraints don't allow the expected arc measure {expected}")
                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message=f"Failed to prove arc measure goal: constraints don't allow the expected value.",
                    details=f"Goal was: MeasureOfArc({arc_name}) = {expected}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")
                return False

            # Now check if any other value is allowed
            temp_solver2 = Solver()
            for c in self.solver.assertions():
                temp_solver2.add(c)

            # Add constraint: arc_var != expected (outside epsilon range)
            temp_solver2.add(Or(arc_var < expected - epsilon, arc_var > expected + epsilon))

            if temp_solver2.check() == sat:
                alt_model = temp_solver2.model()
                alt_value = float(alt_model.eval(arc_var).as_decimal(10).rstrip('?'))

                print(f"Error: The proof doesn't uniquely determine arc measure {goal_arc}.")
                print(f"It could be {expected} but also {alt_value}")

                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message=f"Failed to prove arc measure goal: constraints allow multiple values.",
                    details=f"Goal was: MeasureOfArc({arc_name}) = {expected}, but could also be {alt_value}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")
                return False

            # If we get here, the constraints uniquely determine the value to be expected
            model = self.solver.model()
            calc_expr = model.eval(arc_var)
            val_str = calc_expr.as_decimal(10)
            if val_str.endswith('?'):
                val_str = val_str[:-1]
            calculated_value = float(val_str)
            print(f"Calculated value for MeasureOfArc({arc_name}) is {calculated_value}")
            print(f"Success: Arc measure {goal_arc} is uniquely determined to be {expected}.")
            return True
        else:
            print("Solver constraints unsatisfiable when verifying arc goal.")
            error = GeometricError(
                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                message="Failed to prove arc measure goal: solver is unsatisfiable.",
                details=f"Goal: MeasureOfArc() = {expected}"
            )
            print(f"\nError in {error.tier.name}: {error.message}")
            return False

    def verify_goal_length(self, p1: str, p2: str, expected: float, epsilon: float = 1e-8) -> bool:
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
            # Check if the length is forced to be exactly expected
            temp_solver1 = Solver()
            for c in self.solver.assertions():
                temp_solver1.add(c)

            # Add constraint that length_var == expected (within epsilon)
            temp_solver1.add(And(length_var >= expected - epsilon, length_var <= expected + epsilon))

            # If this is unsat, the constraints don't allow the expected value
            if temp_solver1.check() != sat:
                print(f"Error: Constraints don't allow the expected value {expected}")
                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message=f"Failed to prove length goal: constraints don't allow the expected value.",
                    details=f"Goal was: LengthOfLine({normalized}) = {expected}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")
                return False

            # Now check if any other value is allowed
            temp_solver2 = Solver()
            for c in self.solver.assertions():
                temp_solver2.add(c)

            # Add constraint: length_var != expected (with exact equality check)
            # For floating point values, check if outside epsilon range
            temp_solver2.add(Or(length_var < expected - epsilon, length_var > expected + epsilon))

            # If this is sat, the system allows other values - it's not uniquely determined
            if temp_solver2.check() == sat:
                alt_model = temp_solver2.model()
                alt_value = float(alt_model.eval(length_var).as_decimal(10).rstrip('?'))

                print(f"Error: The proof doesn't uniquely determine {normalized}.")
                print(f"It could be {expected} but also {alt_value}")

                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message=f"Failed to prove length goal: constraints allow multiple values.",
                    details=f"Goal was: LengthOfLine({normalized}) = {expected}, but could also be {alt_value}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")
                return False

            # If we get here, the constraints uniquely determine the value
            print(f"Success: The length {normalized} is uniquely determined to be {expected}.")
            return True
        else:
            print("Solver constraints unsatisfiable when verifying length goal.")
            error = GeometricError(
                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                message=f"Failed to prove length goal: solver is unsatisfiable.",
                details=f"Goal: LengthOfLine({normalized}) = {expected}"
            )
            print(f"\nError in {error.tier.name}: {error.message}")
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
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing angle arguments",
                        details="adjacent_complementary_angle requires two angles"
                    ))

                # Check for collinear points in premise
                if "Collinear" in premise:
                    collinear_match = re.search(r'Collinear\((\w+)\)', premise)
                    if collinear_match:
                        points = collinear_match.group(1)  # e.g. "CDA"
                        # Normalize the points from premise
                        normalized_premise_points = self.normalize_collinear_points(points)

                        # Check if these normalized points exist in collinear_facts
                        collinear_found = False
                        for fact in self.collinear_facts:
                            # Try both original and reversed order
                            fact_forward = self.normalize_collinear_points(''.join(fact))
                            fact_reversed = self.normalize_collinear_points(''.join(fact[::-1]))

                            if normalized_premise_points in [fact_forward, fact_reversed]:
                                collinear_found = True
                                break

                        if not collinear_found:
                            return return_error(GeometricError(
                                tier=ErrorTier.TIER2_PREMISE,
                                message=f"Points {points} are not proven collinear",
                                details=f"Known collinear facts: {self.collinear_facts}"
                            ))

                        # Verify the angles exist
                        angle1, angle2 = args[1], args[2]  # e.g. "CDB", "BDA"

                        # Check that both angles contain the shared point
                        shared_point = None
                        for p in angle1:
                            if p in angle2:
                                shared_point = p
                                break

                        if not shared_point:
                            return return_error(GeometricError(
                                tier=ErrorTier.TIER2_PREMISE,
                                message=f"Angles {angle1} and {angle2} must share a vertex",
                                details="Required for adjacent complementary angles"
                            ))

                        # Check that the shared point is in the collinear set
                        if shared_point not in points:
                            return return_error(GeometricError(
                                tier=ErrorTier.TIER2_PREMISE,
                                message=f"Shared point {shared_point} must be on the collinear line {points}",
                                details="Vertex must be on the collinear line"
                            ))

                        return True, None
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
            elif version == "2":
                print("2")


        elif theorem_name == "cosine_theorem":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing triangle argument for cosine_theorem",
                        details="Expected cosine_theorem(1, triangle)"
                    ))

                triangle = args[1].strip()
                normalized_triangle = self.normalize_triangle(triangle)

                # Check if the triangle exists in the polygons stored in the class attributes
                if normalized_triangle not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Triangle {triangle} not defined in the geometric data",
                        details=f"Known polygons: {self.polygons}"
                    ))

                return True, None

        elif theorem_name == "line_addition":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing arguments for line_addition",
                        details="Expected: line_addition(1, line1, line2)"
                    ))

                line1 = args[1].strip()  # e.g. "CD"
                line2 = args[2].strip()  # e.g. "DA"

                # Extract points from premise collinearity
                collinear_match = re.search(r'Collinear\((\w+)\)', premise)
                if not collinear_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing collinearity fact in premise",
                        details="line_addition requires collinear points"
                    ))

                collinear_points = collinear_match.group(1)  # e.g. "CDA"
                normalized_collinear = self.normalize_collinear_points(collinear_points)

                # Check if collinearity fact exists
                if not any(self.normalize_collinear_points(''.join(fact)) == normalized_collinear
                           for fact in self.collinear_facts):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Points {collinear_points} not proven collinear",
                        details=f"Known collinear facts: {self.collinear_facts}"
                    ))

                # Verify that the lines share points in the collinear sequence
                if not (all(p in collinear_points for p in line1) and
                        all(p in collinear_points for p in line2)):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Lines must be part of the collinear sequence",
                        details=f"Lines {line1} and {line2} must be formed by points in {collinear_points}"
                    ))

                # Check if lines share an endpoint
                common_point = set(line1).intersection(set(line2))
                if not common_point:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Lines must share an endpoint",
                        details=f"Lines {line1} and {line2} must have a common point"
                    ))

                return True, None




        elif theorem_name == "perpendicular_bisector_judgment_distance_equal":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing arguments for perpendicular_bisector_judgment_distance_equal",
                        details="Expected: perpendicular_bisector_judgment_distance_equal(1, bisector_line, bisected_line)"
                    ))

                bisector = args[1].strip()  # e.g. "BD"
                bisected = args[2].strip()  # e.g. "CA"

                # Parse the premise parts
                premise_parts = premise.split('&')

                # Check collinearity fact
                collinear_part = next((p for p in premise_parts if p.startswith('Collinear(')), None)
                if not collinear_part:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing collinearity fact in premise",
                        details="Required for perpendicular bisector"
                    ))

                # Extract collinear points and check
                collinear_match = re.search(r'Collinear\((\w+)\)', collinear_part)
                if collinear_match:
                    collinear_points = collinear_match.group(1)
                    normalized_collinear = self.normalize_collinear_points(collinear_points)
                    if not any(self.normalize_collinear_points(''.join(fact)) == normalized_collinear
                               for fact in self.collinear_facts):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Points {collinear_points} not proven collinear",
                            details=f"Known collinear facts: {self.collinear_facts}"
                        ))

                # Check angle = 90° fact
                angle_eq_part = next((p for p in premise_parts if p.startswith('Equal(MeasureOfAngle(')), None)
                if not angle_eq_part:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing right angle fact in premise",
                        details="Perpendicular bisector requires 90° angle"
                    ))

                # Check angle equality matches required right angle
                angle_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),90\)', angle_eq_part)
                if not angle_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Angle value must be 90 degrees",
                        details="Required for perpendicular bisector"
                    ))

                # Check length equality fact
                length_eq_part = next((p for p in premise_parts if 'LengthOfLine' in p), None)
                if not length_eq_part:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing length equality in premise",
                        details="Required for perpendicular bisector"
                    ))

                # All premise checks passed, return success
                return True, None

        elif theorem_name == "altitude_of_quadrilateral_judgment_diagonal":

            if len(args) < 2:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Missing arguments for altitude_of_quadrilateral_judgment_diagonal"

                ))

            quad = args[1].strip()  # e.g., "DACB"

            # Parse premise to check for parallelogram or trapezoid

            premise_parts = premise.split('&')

            first_part = premise_parts[0].strip('()')  # Remove outer parentheses

            shape_options = first_part.split('|')  # Split on OR operator

            is_valid = False

            for shape_fact in shape_options:

                if shape_fact.startswith('Parallelogram('):

                    para_match = re.match(r'Parallelogram\((\w+)\)', shape_fact)

                    if para_match and para_match.group(1) == quad:

                        if quad in self.parallelograms:
                            is_valid = True

                            break

                elif shape_fact.startswith('Trapezoid('):

                    trap_match = re.match(r'Trapezoid\((\w+)\)', shape_fact)

                    if trap_match and trap_match.group(1) == quad:

                        if hasattr(self, 'trapezoids') and quad in self.trapezoids:

                            # If it's a trapezoid, also check for the right angle

                            angle_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),90\)', premise)

                            if angle_match:

                                angle_name = angle_match.group(1)

                                angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

                                if self.solver.check() == sat:

                                    # Check if the angle is constrained to 90 degrees

                                    temp_solver = Solver()

                                    for c in self.solver.assertions():
                                        temp_solver.add(c)

                                    temp_solver.add(angle_var != 90)

                                    if temp_solver.check() == unsat:
                                        is_valid = True

                                        break

            if not is_valid:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Shape {quad} is not proven to be a parallelogram or a trapezoid with right angle",

                    details=f"Known parallelograms: {self.parallelograms}"

                ))

            return True, None


        elif theorem_name == "altitude_of_quadrilateral_judgment_left_vertex":
            if len(args) < 3:
                return (False, GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing arguments for altitude_of_quadrilateral_judgment_left_vertex."
                ))
            quad = args[2].strip()
            # Check that the quadrilateral is recorded as a parallelogram or trapezoid.
            if not (quad in self.parallelograms or quad in self.trapezoids):
                return (False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Quadrilateral {quad} is not defined as a parallelogram or trapezoid."
                ))

            return (True, None)







        elif theorem_name == "parallelogram_property_opposite_line_equal":
            if len(args) < 2:
                return (False, GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing parallelogram name for parallelogram_property_opposite_line_equal."
                ))
            para = args[1].strip()
            if para not in self.parallelograms:
                return (False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Parallelogram {para} is not defined."
                ))
            return (True, None)

        elif theorem_name == "parallelogram_area_formula_common":
            if len(args) < 2:
                return (False, GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing quadrilateral name for parallelogram_area_formula_common."
                ))
            quad = args[1].strip()
            if quad not in self.parallelograms:
                return (False, GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Quadrilateral {quad} is not defined as a parallelogram."
                ))
            return (True, None)


        elif theorem_name == "isosceles_triangle_property_angle_equal":

            # Expected theorem call: isosceles_triangle_property_angle_equal(1, T)

            # where T is a triangle name (e.g., "JPN").

            if len(args) < 2:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Missing triangle name for isosceles_triangle_property_angle_equal."

                ))

            tri = args[1].strip()  # e.g., "JPN"

            # Generate all cyclic variations of the triangle T.

            def cyclic_variations(s):

                return {s[i:] + s[:i] for i in range(len(s))}

            variations = cyclic_variations(tri)

            # Check that at least one cyclic variation of T is recorded as isosceles.

            if not (variations & self.isosceles_triangles):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Triangle {tri} is not recorded as isosceles.",

                    details="Ensure that isosceles_triangle_judgment_line_equal has been applied."

                ))

            return True, None









        elif theorem_name == "isosceles_triangle_judgment_line_equal":
            # Expected theorem call: isosceles_triangle_judgment_line_equal(1, T)
            # where T is a triangle name (for example, "JPN").
            if len(args) < 2:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing triangle name for isosceles_triangle_judgment_line_equal."
                ))
            tri = args[1].strip()  # e.g., "JPN"

            # Check that the triangle is defined (i.e. a polygon fact exists)


            # We now want to check that the premise contains an equality between two sides
            # sharing a common vertex for some cyclic rotation of tri.
            # For a triangle ABC, one possibility is Equal(LengthOfLine(AB),LengthOfLine(AC)).
            def cyclic_rotations(s):
                rotations = []
                for i in range(len(s)):
                    rotations.append(s[i:] + s[:i])
                return rotations

            rotations = cyclic_rotations(tri)
            found_equality = False



            # Then, in your branch:
            for r in rotations:
                if self.check_length_equality(r[0:2], r[0] + r[2]):
                    found_equality = True
                    break
            if not found_equality:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Expected equality between two sides sharing a vertex not found in the premise.",
                    details=f"Premise: {premise}"
                ))
            return True, None


        elif theorem_name == "rectangle_property_diagonal_equal":

            # Expected theorem call: rectangle_property_diagonal_equal(1, PNML)

            # And the premise should include a clause like "Rectangle(PNML)".

            if len(args) < 2:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Missing rectangle name for rectangle_property_diagonal_equal."

                ))

            rect_name = args[1].strip()  # e.g., "PNML"

            # Check that a rectangle equivalent to rect_name (via cyclic variations) was declared.

            if not (rect_name in self.rectangles):
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Rectangle {rect_name} is not defined.",

                    details=f"Defined rectangles (cyclic variations): {self.rectangles}"

                ))

            # Since the rectangle fact is present, we assume that the diagonal lines will be

            # handled in later steps. Do not check for the existence of the diagonal lines here.

            return True, None


        elif theorem_name == "parallelogram_property_diagonal_bisection":
            # Expected theorem call: parallelogram_property_diagonal_bisection(1, PNML, J)
            # The premise should include a parallelogram fact for PNML and
            # collinear facts showing that the intersection point J lies on both diagonals.
            if len(args) < 3:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Insufficient arguments for parallelogram_property_diagonal_bisection."
                ))
            para_name = args[1].strip()  # e.g., "PNML"
            mid_candidate = args[2].strip()  # e.g., "J"

            # --- Check that a parallelogram fact is recorded for the given parallelogram.
            # (Assume that when parsing TEXT_CDL, all cyclic variations of any parallelogram are added to self.parallelograms.)
            if not (get_cyclic_variations(para_name) & self.parallelograms):
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Parallelogram {para_name} is not defined.",
                    details=f"Defined parallelograms: {self.parallelograms}"
                ))

            # --- Compute the expected collinear facts.
            # For a quadrilateral (parallelogram) with vertices in order, the diagonals are:
            #    diag1: from the 1st vertex to the 3rd, and diag2: from the 2nd vertex to the 4th.
            if len(para_name) < 4:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Parallelogram name {para_name} is invalid (expected 4 letters)."
                ))
            diag1_expected = para_name[0] + mid_candidate + para_name[2]  # e.g., "PJM"
            diag2_expected = para_name[1] + mid_candidate + para_name[3]  # e.g., "NJL"

            norm_diag1 = self.normalize_collinear_points(diag1_expected)
            norm_diag2 = self.normalize_collinear_points(diag2_expected)

            found_diag1 = any(self.normalize_collinear_points("".join(fact)) == norm_diag1
                              for fact in self.collinear_facts)
            found_diag2 = any(self.normalize_collinear_points("".join(fact)) == norm_diag2
                              for fact in self.collinear_facts)

            if not found_diag1 or not found_diag2:
                missing = []
                if not found_diag1:
                    missing.append(diag1_expected)
                if not found_diag2:
                    missing.append(diag2_expected)
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Expected collinear fact(s) {', '.join(missing)} not found.",
                    details=f"Stored collinear facts: {[''.join(f) for f in self.collinear_facts]}"
                ))

            return True, None




        elif theorem_name == "circle_property_circular_power_tangent_and_segment_line":
            # Expected arguments: version, token1, token2, token3.
            # For example: (1, "DC", "DBF", "E")
            version = args[0].strip()  # e.g., "1"
            token1 = args[1].strip()  # e.g., "DC"
            token2 = args[2].strip()  # e.g., "DBF"  (assumed to be a three–letter string)
            token3 = args[3].strip()  # e.g., "E"

            # --- Check that the tangent fact has been recorded.
            if (token1, token3) not in self.tangent_facts:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Tangent fact IsTangentOfCircle({token1},{token3}) not found in accumulated data.",
                    details=f"Stored tangent facts: {self.tangent_facts}"
                ))

            # --- Check that a cocircular fact exists for the chord.
            # For token2, we interpret the chord as token2[1:].
            chord = token2[1:]
            found_cocircular = False
            for fact in self.cocircular_facts:
                # Each cocircular fact is assumed to be stored as a tuple whose first element is the center.
                # Compare the sorted list of chord letters with the sorted version of fact[1:].
                if fact[0] == token3 and sorted(fact[1:]) == sorted(list(chord)):
                    found_cocircular = True
                    break
            if not found_cocircular:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Expected cocircular fact with center {token3} and chord {chord} not found.",
                    details=f"Stored cocircular facts: {self.cocircular_facts}"
                ))

            # --- Check that the secant is recorded as collinear.
            # We expect a collinear fact corresponding to token2.
            normalized_secant = self.normalize_collinear_points(token2)
            found_collinear = False
            for fact in self.collinear_facts:
                if self.normalize_collinear_points("".join(fact)) == normalized_secant:
                    found_collinear = True
                    break
            if not found_collinear:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Expected collinear fact Collinear({token2}) not found.",
                    details=f"Stored collinear facts: {[''.join(f) for f in self.collinear_facts]}"
                ))
            return True, None




        elif theorem_name == "parallel_property_collinear_extend":

            # Validate that the expected collinear fact is present and that the parallel relation exists.

            version = args[0].strip()

            if version not in {"1", "3"}:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message=f"Unsupported version {version} for parallel_property_collinear_extend.",

                    details=f"Version provided: {version}"

                ))

            token1 = args[1].strip()  # e.g., "GA"

            token2 = args[2].strip()  # e.g., "HD"

            token3 = args[3].strip()  # e.g., "J"

            # Determine the expected collinear fact from the tokens.

            if version == "3":

                # Expected: token1[0] + token3 + token1[1]

                expected_collinear = token1[0] + token3 + token1[1]

            elif version == "1":

                # Expected: token3 + token1

                expected_collinear = token3 + token1

            normalized_expected = self.normalize_collinear_points(expected_collinear)

            found_collinear = False

            for fact in self.collinear_facts:

                # Assume each fact is stored as a list of points; join them and normalize.

                normalized_fact = self.normalize_collinear_points("".join(fact))

                if normalized_fact == normalized_expected:
                    found_collinear = True

                    break

            if not found_collinear:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Expected collinear fact Collinear({expected_collinear}) not found.",

                    details=f"Stored collinear facts: {[''.join(f) for f in self.collinear_facts]}"

                ))

            # (Optional:) Also check that a parallel relation between token1 and token2 already exists.

            found_parallel = False

            possible_parallel = {

                (token1, token2),

                (token1[::-1], token2),

                (token1, token2[::-1]),

                (token1[::-1], token2[::-1])

            }

            for pair in self.parallel_pairs:

                if pair in possible_parallel or pair[::-1] in possible_parallel:
                    found_parallel = True

                    break

            if not found_parallel:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Expected parallel relation ParallelBetweenLine({token1},{token2}) not found.",

                    details=f"Stored parallel pairs: {self.parallel_pairs}"

                ))

            # If all checks pass, return success.

            return True, None





        elif theorem_name == "circle_property_circular_power_segment_and_segment_line":
            # Expected arguments: version, token1, token2, token3.
            # For example: (1, "AFB", "AGC", "E")
            version = args[0].strip()  # (unused here but could be used if needed)
            token1 = args[1].strip()  # e.g., "AFB"
            token2 = args[2].strip()  # e.g., "AGC"
            token3 = args[3].strip()  # e.g., "E"

            # --- Check the cocircular facts.
            # For token1, we expect a fact like: Cocircular(E,FB)
            chord1 = token1[1:]  # for "AFB", chord1 = "FB"
            found_cocircular1 = False
            for fact in self.cocircular_facts:
                # Each cocircular fact is stored as a tuple with the center first.
                if fact[0] == token3 and sorted(fact[1:]) == sorted(list(chord1)):
                    found_cocircular1 = True
                    break
            if not found_cocircular1:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Expected cocircular fact Cocircular({token3},{chord1}) not found.",
                    details=f"Stored cocircular facts: {self.cocircular_facts}"
                ))

            # For token2, we expect a fact like: Cocircular(E,GC)
            chord2 = token2[1:]  # for "AGC", chord2 = "GC"
            found_cocircular2 = False
            for fact in self.cocircular_facts:
                if fact[0] == token3 and sorted(fact[1:]) == sorted(list(chord2)):
                    found_cocircular2 = True
                    break
            if not found_cocircular2:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Expected cocircular fact Cocircular({token3},{chord2}) not found.",
                    details=f"Stored cocircular facts: {self.cocircular_facts}"
                ))

            # --- Check the collinearity facts.
            # Expect Collinear(token1) and Collinear(token2) to be present.
            norm_token1 = self.normalize_collinear_points(token1)
            norm_token2 = self.normalize_collinear_points(token2)
            found_collinear1 = any(self.normalize_collinear_points("".join(fact)) == norm_token1
                                   for fact in self.collinear_facts)
            found_collinear2 = any(self.normalize_collinear_points("".join(fact)) == norm_token2
                                   for fact in self.collinear_facts)
            if not found_collinear1:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Expected collinear fact Collinear({token1}) not found.",
                    details=f"Stored collinear facts: {[''.join(f) for f in self.collinear_facts]}"
                ))
            if not found_collinear2:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Expected collinear fact Collinear({token2}) not found.",
                    details=f"Stored collinear facts: {[''.join(f) for f in self.collinear_facts]}"
                ))
            return True, None





        elif theorem_name == "radius_of_circle_property_length_equal":
            # Check that the premise includes a centre fact.
            # Suppose args[2] holds the circle token, e.g. "O".
            circle_token = args[2].strip()
            if circle_token not in self.circle_centers:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Centre for circle {circle_token} not recorded.",
                    details=f"Accumulated centres: {self.circle_centers}"
                ))

            # Optionally, you can also check that a Line fact for the given line is present.
            if "Line(" not in premise:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Premise for radius_of_circle_property_length_equal must include a Line fact.",
                    details=f"Premise provided: {premise}"
                ))
            return True, None

        elif theorem_name == "circle_property_chord_perpendicular_bisect_chord":
            # Extract the circle and points from premise
            cocirc_match = re.search(r'Cocircular\((\w+),(\w+)\)', premise)
            if not cocirc_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing Cocircular fact in premise"
                ))

            circle, points = cocirc_match.groups()
            # Check against stored cocircular facts
            found = False
            for fact in self.cocircular_facts:
                if fact[0] == circle and sorted(fact[1:]) == sorted(list(points)):
                    found = True
                    break

            if not found:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Cocircular fact not established",
                    details=f"Known cocircular facts: {self.cocircular_facts}"
                ))
            return True, None


        elif theorem_name == "midsegment_of_triangle_judgment_parallel":
            version = args[0].strip()
            if version == "2":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Insufficient arguments for midsegment_of_triangle_judgment_parallel",
                        details="Expected: midsegment_of_triangle_judgment_parallel(2, line, triangle)"
                    ))

                line = args[1].strip()  # e.g. "HD"
                tri = args[2].strip()  # e.g. "CFB"

                # Check triangle exists
                if self.normalize_triangle(tri) not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Triangle {tri} not defined",
                        details=f"Known polygons: {self.polygons}"
                    ))

                # Extract collinear facts from premise
                collinear_matches = re.findall(r'Collinear\((\w+)\)', premise)
                if len(collinear_matches) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing required collinear points",
                        details="Midsegment theorem requires two collinear facts"
                    ))

                # Check each collinear fact against stored facts
                for collinear_points in collinear_matches:
                    normalized = self.normalize_collinear_points(collinear_points)
                    if not any(self.normalize_collinear_points(''.join(fact)) == normalized
                               for fact in self.collinear_facts):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Points {collinear_points} not proven collinear",
                            details=f"Known collinear facts: {self.collinear_facts}"
                        ))

                # Extract and check parallel fact
                parallel_match = re.search(r'ParallelBetweenLine\((\w+),(\w+)\)', premise)
                if not parallel_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing parallel line relation",
                        details="Midsegment theorem requires parallel lines"
                    ))

                line1, line2 = parallel_match.groups()
                possible_pairs = [
                    (line1, line2),
                    (line2, line1),
                    (line1[::-1], line2),
                    (line1, line2[::-1]),
                    (line2[::-1], line1),
                    (line2, line1[::-1])
                ]

                if not any(pair in self.parallel_pairs for pair in possible_pairs):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Lines {line1} and {line2} not proven parallel",
                        details=f"Known parallel pairs: {self.parallel_pairs}"
                    ))

                # Extract and check length equality
                length_match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', premise)
                if not length_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing length equality",
                        details="Midsegment theorem requires equal lengths"
                    ))

                length1, length2 = length_match.groups()
                if not self.check_length_equality(length1, length2):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Lengths {length1} and {length2} not proven equal",
                        details="Required for midsegment theorem"
                    ))

                return True, None





        elif theorem_name == "arc_length_formula":

            arc_match = re.search(r'Arc\((\w+)\)', premise)

            if not arc_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing arc definition"

                ))

            arc_name = arc_match.group(1)

            normalized_arc = self.normalize_arc(arc_name)

            if f"arc_{normalized_arc}" not in self.arcs:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Arc {arc_name} not established",

                    details=f"Known arcs: {list(self.arcs.keys())}"

                ))

            return True, None


        elif theorem_name == "arc_property_circumference_angle_internal":
            # Extract angle from premise
            angle_match = re.search(r'Angle\((\w{3})\)', premise)
            if not angle_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing angle in premise"
                ))

            return True, None


        elif theorem_name == "parallel_property_ipsilateral_internal_angle":
            # The premise should include a ParallelBetweenLine clause and a Line clause.
            parallel_match = re.search(r'ParallelBetweenLine\((\w+),(\w+)\)', premise)
            if not parallel_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing parallel lines in premise"
                ))

            line1, line2 = parallel_match.groups()
            # Check against stored parallel pairs
            possible_pairs = (line1, line2)


            if not possible_pairs in self.parallel_pairs :
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Lines {line1} and {line2} not proven parallel",
                    details=f"Known parallel pairs: {self.parallel_pairs}"
                ))
            return True, None


        elif theorem_name == "circle_property_circular_power_segment_and_segment_angle":

            # Extract the cocircular fact tokens from the premise.

            cocirc_match = re.search(r'Cocircular\((\w),(\w+)\)', premise)

            if not cocirc_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Premise is missing a valid Cocircular(...) fact.",

                    details=f"Premise provided: {premise}"

                ))

            circle_token, arc_group_token = cocirc_match.groups()  # e.g. 'B' and 'SUVT'

            # Check generically: for each stored cocircular fact (stored as a tuple),

            # see if the first element equals the circle token and the remaining elements,

            # when sorted, match the sorted list of letters in the arc group.

            found = False

            for fact in self.cocircular_facts:

                # fact is a tuple like ('B', 'S', 'U', 'V', 'T')—or possibly in some order.

                if fact[0] == circle_token and sorted(fact[1:]) == sorted(list(arc_group_token)):
                    found = True

                    break

            if not found:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Cocircular({circle_token},{arc_group_token}) not established",

                    details=f"Accumulated cocircular facts: {self.cocircular_facts}"

                ))

            # Similarly, do a generic check for the collinear facts.

            # For example, if the theorem call also requires Collinear(RST):

            collinear_match1 = re.search(r'Collinear\((\w+)\)', premise)

            if collinear_match1:

                collinear_token = collinear_match1.group(1)

                found_coll = any(
                    self.normalize_collinear_points(''.join(fact)) == self.normalize_collinear_points(collinear_token)

                    for fact in self.collinear_facts)

                if not found_coll:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"Collinear({collinear_token}) not established",

                        details=f"Known collinear facts: {self.collinear_facts}"

                    ))

            # (Repeat as needed for any additional required collinear facts.)

            return True, None





        elif theorem_name == "triangle_perimeter_formula":
            # Check that the premise contains a valid triangle.
            # Expecting something like: Polygon(ABC)
            poly_match = re.search(r'Polygon\((\w+)\)', premise)
            if not poly_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing or invalid Polygon() in premise for sine_theorem"
                ))
            return True, None




        elif theorem_name == "tangent_of_circle_property_perpendicular":

            # Expected premise (from the theorem‐sequence) is something like:

            # "IsTangentOfCircle(AN,O)&Angle(ANO)&IsCentreOfCircle(O,O)"

            # Instead of merely checking for substring membership, we extract and then check

            # that these facts have already been accumulated.

            # Check for the tangent fact.

            tan_m = re.search(r'IsTangentOfCircle\((\w+),(\w+)\)', premise)

            if not tan_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing IsTangentOfCircle(...) in premise for tangent_of_circle_property_perpendicular",

                    details=f"Premise provided: {premise}"

                ))

            tangent_line_from_premise, center_from_tangent = tan_m.group(1), tan_m.group(2)

            if (tangent_line_from_premise, center_from_tangent) not in self.tangent_facts:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Tangent fact IsTangentOfCircle({tangent_line_from_premise},{center_from_tangent}) not established",

                    details=f"Accumulated tangent facts: {self.tangent_facts}"

                ))

            # Check for an angle fact.

            angle_m = re.search(r'Angle\((\w{3})\)', premise)

            if not angle_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing Angle(...) in premise for tangent_of_circle_property_perpendicular",

                    details=f"Premise provided: {premise}"

                ))

            angle_str = angle_m.group(1)

            normalized_angle = self.normalize_angle_name(angle_str)

            # Check for the centre fact.

            centre_m = re.search(r'IsCentreOfCircle\((\w+),(\w+)\)', premise)

            if not centre_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing IsCentreOfCircle(...) in premise for tangent_of_circle_property_perpendicular",

                    details=f"Premise provided: {premise}"

                ))

            centre_from_fact = centre_m.group(1)

            if centre_from_fact not in self.circle_centers:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Centre {centre_from_fact} not established",

                    details=f"Accumulated centres: {self.circle_centers}"

                ))

            return True, None


        elif theorem_name == "arc_property_center_angle":

            # Expected premise: e.g. "Arc(OMN)&Angle(NOM)&IsCentreOfCircle(O,O)"

            # Extract the arc fact.

            arc_m = re.search(r'Arc\((\w{3})\)', premise)

            if not arc_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing Arc(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            arc_name = arc_m.group(1)

            normalized_arc = self.normalize_arc(arc_name)

            if f"arc_{normalized_arc}" not in self.arcs:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Arc {arc_name} not established",

                    details=f"Accumulated arcs: {list(self.arcs.keys())}"

                ))

            # Check for an angle fact.

            angle_m = re.search(r'Angle\((\w{3})\)', premise)

            if not angle_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing Angle(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            angle_str = angle_m.group(1)

            normalized_angle = self.normalize_angle_name(angle_str)

            # Check for the centre fact.

            centre_m = re.search(r'IsCentreOfCircle\((\w+),(\w+)\)', premise)

            if not centre_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing IsCentreOfCircle(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            centre_from_fact = centre_m.group(1)

            if centre_from_fact not in self.circle_centers:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Centre {centre_from_fact} not established",

                    details=f"Accumulated centres: {self.circle_centers}"

                ))

            return True, None


        elif theorem_name == "arc_property_circumference_angle_external":

            # Expected premise: e.g. "Cocircular(O,MNB)&Angle(NBM)"

            # Extract the cocircular fact.

            cocirc_m = re.search(r'Cocircular\((\w+),(\w+)\)', premise)

            if not cocirc_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing Cocircular(...) in premise for arc_property_circumference_angle_external",

                    details=f"Premise provided: {premise}"

                ))

            circle_from_cocirc = cocirc_m.group(1)

            points_str = cocirc_m.group(2)

            found = False

            for fact in self.cocircular_facts:

                # Assume each cocircular fact is stored as a tuple with the circle as first element

                # and the remaining letters as the points on the circle.

                if fact[0] == circle_from_cocirc and sorted(fact[1:]) == sorted(list(points_str)):
                    found = True

                    break

            if not found:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Cocircular({circle_from_cocirc},{points_str}) not established",

                    details=f"Accumulated cocircular facts: {self.cocircular_facts}"

                ))

            # Check for an angle fact.

            angle_m = re.search(r'Angle\((\w{3})\)', premise)

            if not angle_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing Angle(...) in premise for arc_property_circumference_angle_external",

                    details=f"Premise provided: {premise}"

                ))

            angle_str = angle_m.group(1)

            normalized_angle = self.normalize_angle_name(angle_str)

            # if f"angle_{normalized_angle}" not in self.angles:
            #     return return_error(GeometricError(
            #
            #         tier=ErrorTier.TIER2_PREMISE,
            #
            #         message=f"Angle {angle_str} not established",
            #
            #         details=f"Accumulated angles: {list(self.angles.keys())}"
            #
            #     ))

            return True, None



        elif theorem_name == "arc_property_center_angle":

            # Expected premise: e.g. "Arc(OMN)&Angle(NOM)&IsCentreOfCircle(O,O)"

            # Extract the arc fact.

            arc_m = re.search(r'Arc\((\w{3})\)', premise)

            if not arc_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing Arc(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            arc_name = arc_m.group(1)

            normalized_arc = self.normalize_arc(arc_name)

            if f"arc_{normalized_arc}" not in self.arcs:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Arc {arc_name} not established",

                    details=f"Accumulated arcs: {list(self.arcs.keys())}"

                ))

            # Check for an angle fact.

            angle_m = re.search(r'Angle\((\w{3})\)', premise)

            if not angle_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing Angle(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            angle_str = angle_m.group(1)

            normalized_angle = self.normalize_angle_name(angle_str)

            if f"angle_{normalized_angle}" not in self.angles:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Angle {angle_str} not established",

                    details=f"Accumulated angles: {list(self.angles.keys())}"

                ))

            # Check for the centre fact.

            centre_m = re.search(r'IsCentreOfCircle\((\w+),(\w+)\)', premise)

            if not centre_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing IsCentreOfCircle(...) in premise for arc_property_center_angle",

                    details=f"Premise provided: {premise}"

                ))

            centre_from_fact = centre_m.group(1)

            if centre_from_fact not in self.circle_centers:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Centre {centre_from_fact} not established",

                    details=f"Accumulated centres: {self.circle_centers}"

                ))

            return True, None


        elif theorem_name == "arc_property_circumference_angle_external":

            # Expected premise: e.g. "Cocircular(O,MNB)&Angle(NBM)"

            # Extract the cocircular fact.

            cocirc_m = re.search(r'Cocircular\((\w+),(\w+)\)', premise)

            if not cocirc_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing Cocircular(...) in premise for arc_property_circumference_angle_external",

                    details=f"Premise provided: {premise}"

                ))

            circle_from_cocirc = cocirc_m.group(1)

            points_str = cocirc_m.group(2)

            found = False

            for fact in self.cocircular_facts:

                # Assume each cocircular fact is stored as a tuple with the circle as first element

                # and the remaining letters as the points on the circle.

                if fact[0] == circle_from_cocirc and sorted(fact[1:]) == sorted(list(points_str)):
                    found = True

                    break

            if not found:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Cocircular({circle_from_cocirc},{points_str}) not established",

                    details=f"Accumulated cocircular facts: {self.cocircular_facts}"

                ))

            # Check for an angle fact.

            angle_m = re.search(r'Angle\((\w{3})\)', premise)

            if not angle_m:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing Angle(...) in premise for arc_property_circumference_angle_external",

                    details=f"Premise provided: {premise}"

                ))

            angle_str = angle_m.group(1)

            normalized_angle = self.normalize_angle_name(angle_str)

            if f"angle_{normalized_angle}" not in self.angles:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Angle {angle_str} not established",

                    details=f"Accumulated angles: {list(self.angles.keys())}"

                ))

            return True, None






        elif theorem_name == "sine_theorem":
            # Check that the premise contains a valid triangle.
            # Expecting something like: Polygon(ABC)
            poly_match = re.search(r'Polygon\((\w+)\)', premise)
            if not poly_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing or invalid Polygon() in premise for sine_theorem"
                ))
            triangle_points = poly_match.group(1)
            if len(triangle_points) != 3:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Polygon({triangle_points}) does not represent a triangle (3 vertices expected)"
                ))
            # Optionally, if the theorem call provides a triangle (as args[1]),
            # verify that it matches the Polygon fact.
            if len(args) >= 2 and args[1].strip() != triangle_points:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Polygon in premise ({triangle_points}) does not match the triangle in theorem call ({args[1].strip()})"
                ))
            return True, None


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
            # 2) check Cocircular(...) e.g. Cocircular(D,BCA)
            cocirc_m = re.search(r'Cocircular\((\w+),(\w+)\)', premise)
            if not cocirc_m:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing Cocircular(...) in premise"
                ))
            circle_from_cocirc, points_str = cocirc_m.groups()
            # For example, for "Cocircular(D,BCA)" we have circle_from_cocirc == "D" and points_str == "BCA"
            # Now check if a matching cocircular fact exists.
            found_cocirc = False
            for ctuple in self.cocircular_facts:
                # Assume that each cocircular fact is stored as a tuple with the circle as first element
                # For example, a stored fact might be ('D', 'B', 'C', 'A')
                if ctuple[0] == circle_from_cocirc and len(ctuple) == len(points_str) + 1:
                    # Compare the remaining points in a sorted way so that the order doesn't matter.
                    if sorted(ctuple[1:]) == sorted(points_str):
                        found_cocirc = True
                        break
            if not found_cocirc:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Cocircular({circle_from_cocirc},{points_str}) was not established"
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





        elif theorem_name == "right_triangle_property_pythagorean":
            version = args[0]
            if version == "1":
                # Expecting a theorem call like: right_triangle_property_pythagorean(1, GHE)

                # and that the triangle has already been recorded as a right triangle.

                if len(args) < 2:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Missing triangle argument for right_triangle_property_pythagorean",

                        details="Expected right_triangle_property_pythagorean(1, triangle)"

                    ))

                triangle = args[1].strip()

                # Instead of scanning the premise string, check the recorded right triangles.

                if self.normalize_triangle(triangle) not in self.right_triangles:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"RightTriangle({triangle}) is not recorded.",

                        details=f"Recorded right triangles: {self.right_triangles}"

                    ))

                return True, None
            elif version == "2":
                print("2")




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


        elif theorem_name == "right_triangle_judgment_angle":
            # Expecting something like: "Polygon(GHE)&Equal(MeasureOfAngle(GHE),90)"
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing triangle argument for right_triangle_judgment_angle",
                        details="Expected right_triangle_judgment_angle(1, triangle)"
                    ))
                triangle = args[1].strip()
                # Check that a Polygon fact exists for this triangle.
                polygon_found = False
                # Also check that an angle measure equality specifying 90° is present.
                angle_90_found = False
                # Split the premise on '&' to get the individual facts.
                for conj in premise.split('&'):
                    conj = conj.strip()
                    # Check for the polygon fact:
                    if conj.startswith("Polygon("):
                        m_poly = re.match(r'Polygon\((\w+)\)', conj)
                        if m_poly:
                            poly_name = m_poly.group(1)
                            # Normalize both names so that e.g. "GHE" and "HEG" are equivalent.
                            if self.normalize_triangle(poly_name) in self.polygons:
                                polygon_found = True
                    # Check for the angle equality specifying 90°
                    elif conj.startswith("Equal(MeasureOfAngle("):
                        m_angle = re.match(r'Equal\(MeasureOfAngle\((\w+)\),\s*(\d+)\)', conj)
                        if m_angle:
                            angle_str = m_angle.group(1)
                            angle_val = int(m_angle.group(2))

                            # Check if this angle is related to the triangle
                            if any(p in angle_str for p in triangle):
                                # Get or create the angle variable
                                angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])

                                # Check if angle is constrained to be 90 in the Z3 model
                                if self.solver.check() == sat:
                                    temp_solver = Solver()
                                    for c in self.solver.assertions():
                                        temp_solver.add(c)

                                    # Try to find a solution where the angle is not 90
                                    temp_solver.add(angle_var != 90)

                                    if temp_solver.check() == unsat:
                                        # If unsatisfiable, the angle must be exactly 90
                                        angle_90_found = True
                                        print(
                                            f"Verified angle {angle_str} is constrained to be 90 degrees in the model.")
                                    else:
                                        # The angle could be something other than 90
                                        alt_model = temp_solver.model()
                                        alt_val = float(alt_model.eval(angle_var).as_decimal(10).rstrip('?'))
                                        print(
                                            f"Warning: Angle {angle_str} is not constrained to be 90 degrees. Could also be {alt_val}.")
                                else:
                                    print(f"Warning: Solver is unsatisfiable when checking angle {angle_str}.")
                if not polygon_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Polygon fact for triangle {triangle} is missing in the premise.",
                        details=f"Premise provided: {premise}"
                    ))
                if not angle_90_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Angle measure 90° for triangle {triangle} is not established in the premise.",
                        details=f"Premise provided: {premise}"
                    ))
                return True, None
            elif version == "2":
                print("2")


        elif theorem_name == "triangle_property_angle_sum":
            # Check that the premise contains a valid Polygon fact.
            version = args[0]
            if version == "1":
                poly_match = re.search(r'Polygon\((\w+)\)', premise)
                if not poly_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing or invalid Polygon() in premise for triangle_property_angle_sum"
                    ))
                triangle_points = poly_match.group(1)
                if len(triangle_points) != 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Polygon({triangle_points}) does not represent a triangle (3 vertices expected)"
                    ))
                # Optionally, check that the triangle provided in the theorem call (e.g., args[1]) matches the Polygon.
                if len(args) >= 2 and args[1].strip() != triangle_points:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Polygon in premise ({triangle_points}) does not match the triangle in theorem call ({args[1].strip()})"
                    ))
                # Premise is valid.
                return True, None
            elif version == "2":
                return True, None






        elif theorem_name == "mirror_similar_triangle_judgment_aa":

            if len(args) < 3:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Insufficient arguments for mirror_similar_triangle_judgment_aa",

                    details="Expected mirror_similar_triangle_judgment_aa(1, triangle1, triangle2)"

                ))

            triangle1 = args[1].strip()

            triangle2 = args[2].strip()

            if self.normalize_triangle(triangle1) not in self.polygons:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Polygon for triangle {triangle1} is missing",

                    details="The construction data did not define this polygon."

                ))

            if self.normalize_triangle(triangle2) not in self.polygons:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Polygon for triangle {triangle2} is missing",

                    details="The construction data did not define this polygon."

                ))

            # Check that the premise includes the required angle equalities.

            # For example, in the given premise:

            #   "Polygon(EGH)&Polygon(FEG)&Equal(MeasureOfAngle(EGH),MeasureOfAngle(EGF))&Equal(MeasureOfAngle(GHE),MeasureOfAngle(FEG))"

            # we want to check that the angle equalities hold.

            conjuncts = [p.strip() for p in premise.split('&')]

            for conj in conjuncts:

                if conj.startswith("Equal(MeasureOfAngle("):

                    m = re.match(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conj)

                    if m:

                        ang1 = m.group(1)

                        ang2 = m.group(2)

                        # Use your existing helper to check that these angles are forced equal.

                        if not self.check_angle_equality(ang1, ang2):
                            return return_error(GeometricError(

                                tier=ErrorTier.TIER2_PREMISE,

                                message=f"Premise angle equality {ang1} = {ang2} does not hold.",

                                details="The constraints do not force these two angles to be equal."

                            ))

                    else:

                        return return_error(GeometricError(

                            tier=ErrorTier.TIER2_PREMISE,

                            message=f"Angle equality clause '{conj}' is not in the expected format.",

                            details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"

                        ))

            return True, None


        elif theorem_name == "mirror_similar_triangle_property_line_ratio":
            similar_match = re.search(r'MirrorSimilarBetweenTriangle\((\w+),(\w+)\)', premise)
            if not similar_match:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message="Missing MirrorSimilarBetweenTriangle(...) in premise",
                    details="mirror_similar_triangle_property_line_ratio requires mirror similar triangles"
                ))
            tri1, tri2 = similar_match.groups()
            canonical_pair = self.canonicalize_mirror_triangle_pair(tri1, tri2)
            if canonical_pair not in self.mirror_similar_triangles:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Triangles {tri1} and {tri2} are not proven mirror similar",
                    details=f"Known mirror similar triangles: {self.mirror_similar_triangles}"
                ))




        elif theorem_name == "parallel_property_corresponding_angle":

            version = args[0]

            # Common check: the premise must include a ParallelBetweenLine fact.

            if "ParallelBetweenLine" not in premise:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Missing parallel lines in premise",

                    details="parallel_property_corresponding_angle theorem requires ParallelBetweenLine(...)"

                ))

            line_match = re.search(r'ParallelBetweenLine\(\s*(\w+)\s*,\s*(\w+)\s*\)', premise)

            if not line_match:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message="Invalid parallel lines format in premise"

                ))

            line1, line2 = line_match.group(1), line_match.group(2)

            # Check that these lines are recorded as parallel

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

            # For version 2 we require an additional collinearity fact.

            if version == "2":

                # In our sample for version 2, the theorem call is parallel_property_corresponding_angle(2,HD,FB,A)

                # and the premise includes a Collinear fact—for instance, "Collinear(HFA)".

                token4 = args[3]  # e.g. "A"

                collinear_match = re.search(r'Collinear\(\s*(\w+)\s*\)', premise)

                if collinear_match:

                    points = collinear_match.group(1)

                    if token4 not in points:
                        return return_error(GeometricError(

                            tier=ErrorTier.TIER2_PREMISE,

                            message=f"Premise for version 2 must include a Collinear fact containing '{token4}'",

                            details=f"Premise provided: {premise}"

                        ))

                else:

                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message="Premise for version 2 must include a Collinear fact.",

                        details=f"Premise provided: {premise}"

                    ))

            return True, None





        elif theorem_name == "similar_triangle_property_line_ratio":

            version = args[0]

            if version == "1":

                similar_match = re.search(r'SimilarBetweenTriangle\((\w+),(\w+)\)', premise)

                if not similar_match:
                    # Add return here

                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message="Missing similar triangles in premise",

                        details="similar_triangle_property_line_ratio requires similar triangles"

                    ))

                tri1, tri2 = similar_match.groups()

                if not self.are_triangles_similar(tri1, tri2):
                    # Add return here

                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"Triangles {tri1} and {tri2} are not proven similar",

                        details=f"Known similar triangles: {self.similar_triangles}"

                    ))

                # If all checks pass, return success

                return True, None

            elif version == "2":

                print("2")


        elif theorem_name == "parallelogram_property_opposite_angle_equal":

            version = args[0]
            if version == "1":
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
                return True, None
            elif version == "2":
                print("2")





        elif theorem_name == "similar_triangle_judgment_aa":
            version = args[0]
            if version == "1":
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
            elif version == "2":
                print("2")





        elif theorem_name == "parallel_property_alternate_interior_angle":

            version = args[0]

            if version == "1":

                # Version 1: we require that a ParallelBetweenLine fact is present.

                if "ParallelBetweenLine" not in premise:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message="Missing parallel lines in premise (version 1)",

                        details="parallel_property_alternate_interior_angle requires ParallelBetweenLine(...)"

                    ))

                line_match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', premise)

                if not line_match:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message="Invalid parallel lines format in premise (version 1)"

                    ))

                # (Optionally, you can check that these lines are already recorded as parallel.)

                line1, line2 = line_match.group(1), line_match.group(2)

                possible_pairs = [

                    (line1, line2),

                    (line2, line1),

                    (line1[::-1], line2),

                    (line1, line2[::-1]),

                    (line2[::-1], line1),

                    (line2, line1[::-1])

                ]

                if not any(
                        (pair in self.parallel_pairs or pair[::-1] in self.parallel_pairs) for pair in possible_pairs):
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"Lines {line1} and {line2} not proven parallel (version 1)",

                        details=f"Available parallel pairs: {self.parallel_pairs}"

                    ))

                # Premise is valid for version 1.

                return True, None

            elif version == "2":

                # Version 2: we require both a ParallelBetweenLine fact and an additional Line fact.

                if "ParallelBetweenLine" not in premise:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message="Missing parallel lines in premise (version 2)",

                        details=f"Premise provided: {premise}"

                    ))

                if "Line(" not in premise:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message="Missing Line fact in premise (version 2)",

                        details=f"Premise provided: {premise}"

                    ))

                # (Optionally, further checks can be added here.)

                return True, None


        elif theorem_name == "angle_addition":
            version = args[0]

            if version == "1":
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
                return True, None
            elif version == "2":
                print("2")


        elif theorem_name == "quadrilateral_property_angle_sum":

            if len(args) < 2:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Missing quadrilateral name"

                ))

            quad_name = args[1].strip()

            if quad_name not in self.polygons:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Quadrilateral {quad_name} not defined",

                    details=f"Known polygons: {self.polygons}"

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



            # just a scan
            normal_collinear_set = set()
            if 'CONSTRUCTION_CDL' in sections:
                for line in sections['CONSTRUCTION_CDL']:
                    if line.startswith('Collinear('):
                        points = line[10:-1]  # Extract points from "Collinear(...)"
                        normalized_points = self.normalize_collinear_points(points)
                        # Here we use ''.join(...) as a simple string representation
                        normal_collinear_set.add(''.join(normalized_points))
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


                    if line.startswith('Parallelogram('):
                        match = re.match(r'Parallelogram\((\w+)\)', line)
                        if match:
                            para_name = match.group(1)
                            print(f"Found parallelogram in TEXT_CDL: {para_name}")
                            self.parallelograms.update(get_cyclic_variations(para_name))
                            print(f"Added parallelogram variations: {self.parallelograms}")

                    if line.startswith('Collinear('):
                        points = line[10:-1]  # Extract points from "Collinear(...)"
                        normalized_points = self.normalize_collinear_points(points)
                        normalized_str = ''.join(normalized_points)
                        # If the same fact appears in the main CONSTRUCTION_CDL section, skip it.
                        if normalized_str in normal_collinear_set:
                            print(f"Skipping duplicate collinear fact from extended section: {normalized_points}")
                            continue
                        # Otherwise, add it:
                        self.collinear_facts.append(list(normalized_points))
                        self.add_collinear_fact(list(normalized_points))
                        print(f"Added normalized collinear points (extended): {normalized_points}")


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


                    elif line.startswith("Arc("):
                        # Extract the arc name from e.g. "Arc(OBM)"
                        arc_name = line[4:-1].strip()
                        self.add_arc(arc_name)

                    if line.startswith('Polygon('):
                        # Extract the polygon name; for instance, "ABC" from "Polygon(ABC)"
                        poly_match = re.match(r'Polygon\((\w+)\)', line)
                        if poly_match:
                            poly = poly_match.group(1)
                            # Normalize if you like (so that 'ABC' and 'BCA' are considered the same)
                            normalized_poly = self.normalize_triangle(poly) if len(poly) == 3 else poly
                            self.polygons.add(normalized_poly)
                            print(f"Added polygon: {normalized_poly}")





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

                        # e.g. line = "Cocircular(B,UVTS)"

                        inside = line[11:-1]  # This will be "B,UVTS"

                        raw_fields = inside.split(',')

                        points = []

                        for token in raw_fields:

                            token = token.strip()

                            # If token length > 1, expand into individual letters.

                            if len(token) > 1:

                                points.extend(list(token))

                            else:

                                points.append(token)

                        # Now create a canonical representation.

                        # For example, assume the first letter is fixed and sort the rest.

                        if points:

                            fixed = points[0]

                            others = sorted(points[1:])

                            canonical = (fixed,) + tuple(others)

                        else:

                            canonical = tuple(points)

                        self.cocircular_facts.append(canonical)

                        print(f"Added cocircular fact (canonical): {canonical}")





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
                from fractions import Fraction
                for line in sections['TEXT_CDL']:
                    if line.startswith('Equal(MeasureOfAngle('):
                        match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                        if match:
                            angle_name, expression = match.group(1), match.group(2).strip()
                            print(f"Found angle expression in TEXT_CDL: {angle_name} = {expression}")
                            self.add_algebraic_angle(angle_name, expression)
                    elif line.startswith('Equal(LengthOfLine('):
                        # Try first to match length equality between two lines
                        equality_match = re.match(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', line)
                        if equality_match:
                            line1, line2 = equality_match.groups()
                            print(f"Found length equality in TEXT_CDL: {line1} = {line2}")
                            # Get variables for both lines
                            len1 = self.add_length(line1[0], line1[1])
                            len2 = self.add_length(line2[0], line2[1])
                            # Add equality constraint
                            self.solver.add(len1 == len2)
                            print(f"Added length equality constraint: {line1} = {line2}")
                            continue

                        # If not equality between lines, try the existing case for numeric/algebraic values
                        match = re.match(r'Equal\(LengthOfLine\((\w+)\),(.+)\)', line)
                        if match:
                            line_name, expression = match.groups()
                            expression = expression.strip()
                            print(f"Found length expression in TEXT_CDL: {line_name} = {expression}")
                            # Get (or create) the length variable
                            length_var = self.add_length(line_name[0], line_name[1])

                            try:
                                # Try parsing as numeric value first with math functions
                                import math
                                # Create a safe evaluation environment with only math functions
                                eval_env = {"sqrt": math.sqrt, "pi": math.pi}
                                value = float(eval(expression, {"__builtins__": {}}, eval_env))
                                self.solver.add(length_var == value)
                                print(f"Added numeric length constraint: {line_name} = {value}")
                            except Exception as e:
                                print(f"Could not evaluate as numeric: {expression}. Error: {e}")
                                # Handle as algebraic expression
                                variables = self.extract_variables(expression)
                                for var in variables:
                                    if var not in self.variables:
                                        self.variables[var] = Real(var)
                                        print(f"Created new variable for algebraic length: {var}")
                                expr = self.parse_algebraic_expression(expression)
                                self.solver.add(length_var == expr)
                                print(f"Added algebraic length constraint: {line_name} = {expr}")


                    elif line.startswith('ParallelBetweenLine('):

                        match = re.search(r'ParallelBetweenLine\((\w+),\s*(\w+)\)', line)

                        if match:

                            line1, line2 = match.group(1), match.group(2)

                            # Create the variants: original and reversed

                            variants1 = [line1, line1[::-1]]

                            variants2 = [line2, line2[::-1]]

                            # Add every combination in both orders

                            for v1 in variants1:

                                for v2 in variants2:
                                    self.parallel_pairs.add((v1, v2))

                                    self.parallel_pairs.add((v2, v1))

                            print(f"Added all combinations: {self.parallel_pairs}")



                    elif line.startswith('Equal(DiameterOfCircle('):
                        # This should match a line like: Equal(DiameterOfCircle(A),10)
                        match = re.match(r'Equal\(DiameterOfCircle\((\w+)\),\s*(.+)\)', line)
                        if match:
                            circle_name, expression = match.groups()
                            expression = expression.strip()
                            print(
                                f"Found diameter expression in TEXT_CDL: DiameterOfCircle({circle_name}) = {expression}")
                            # Try to parse the expression as a number first
                            try:
                                value = float(expression)
                                print(f"Adding numeric diameter for circle {circle_name}: {value}")
                            except ValueError:
                                # Otherwise, extract any variables and parse as an algebraic expression.
                                variables = self.extract_variables(expression)
                                for var in variables:
                                    if var not in self.variables:
                                        self.variables[var] = Real(var)
                                        print(f"Created new variable for algebraic diameter: {var}")
                                value = self.parse_algebraic_expression(expression)
                                print(f"Adding algebraic diameter for circle {circle_name}: {value}")
                            diam_name = f"diameter_{circle_name}"
                            if diam_name not in self.circle_diameters:
                                self.circle_diameters[diam_name] = Real(diam_name)
                                self.solver.add(self.circle_diameters[diam_name] >= 0)
                                print(f"Created diameter variable: {diam_name}")
                            self.solver.add(self.circle_diameters[diam_name] == value)
                            print(f"Added constraint: {diam_name} == {value}")


                    elif line.startswith('Equal(MeasureOfArc('):
                        match = re.match(r'Equal\(MeasureOfArc\((\w+)\),(.+)\)', line)
                        if match:
                            arc_name, expression = match.group(1), match.group(2).strip()
                            print(f"Found arc expression in TEXT_CDL: {arc_name} = {expression}")
                            self.add_algebraic_arc(arc_name, expression)
                    # --- New branch for division of line lengths:
                    elif line.startswith('Equal(Div(LengthOfLine('):
                        # This should match a line like:
                        # Equal(Div(LengthOfLine(AD),LengthOfLine(AE)),4)
                        match = re.match(r'Equal\(Div\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\),(.+)\)', line)
                        if match:
                            line1, line2, expression = match.groups()
                            expression = expression.strip()
                            print(
                                f"Found division length expression in TEXT_CDL: Div(LengthOfLine({line1}),LengthOfLine({line2})) = {expression}")
                            # Get the two length variables (assuming the tokens have two letters)
                            len1 = self.add_length(line1[0], line1[1])
                            len2 = self.add_length(line2[0], line2[1])
                            try:
                                expr_val = float(eval(expression, {"pi": 3.141592653589793}))
                            except Exception:
                                expr_val = float(Fraction(expression))
                            self.solver.add(len1 / len2 == expr_val)
                            print(f"Added length division constraint: {line1}/{line2} == {expr_val}")
                        else:
                            print("Error parsing Div(LengthOfLine(...)) expression in TEXT_CDL.")
                    # --- New branch for median facts:
                    elif line.startswith("IsMedianOfTriangle("):
                        # Matches a fact like: IsMedianOfTriangle(AD,ABC)
                        match = re.match(r'IsMedianOfTriangle\((\w+),(\w+)\)', line)
                        if match:
                            median_line, triangle = match.groups()
                            if not hasattr(self, "medians"):
                                self.medians = []
                            self.medians.append((median_line, triangle))
                            print(f"Recorded median: IsMedianOfTriangle({median_line},{triangle})")
                        else:
                            print("Error parsing IsMedianOfTriangle fact in TEXT_CDL.")
                    elif line.startswith('PerpendicularBetweenLine('):
                        match = re.match(r'PerpendicularBetweenLine\((\w+),\s*(\w+)\)', line)
                        if match:
                            line1, line2 = match.group(1), match.group(2)
                            print(f"Found perpendicular lines: {line1} ⊥ {line2}")
                            self.perpendicular_pairs.add((line1, line2))
                            self.perpendicular_pairs.add((line2, line1))
                            vertex = next(p for p in line1 if p in line2)
                            first_point = next(p for p in line2 if p != vertex)
                            last_point = next(p for p in line1 if p != vertex)
                            angle = f"{first_point}{vertex}{last_point}"
                            normalized_angle = self.normalize_angle_name(angle)
                            angle_var = self.add_angle(first_point, vertex, last_point)
                            self.solver.add(angle_var == 90)
                            print(f"Added 90° perpendicular angle constraint: {normalized_angle}")
                    elif line.startswith("Square("):
                        match = re.match(r"Square\((\w+)\)", line)
                        if match:
                            shape_name = match.group(1)
                            self.squares.add(shape_name)
                            self.impose_square_constraints(shape_name)
                    elif line.startswith("IsTangentOfCircle("):
                        m = re.match(r'IsTangentOfCircle\((\w+),(\w+)\)', line)
                        if m:
                            tangent_line, circle_name = m.groups()
                            self.tangent_facts.add((tangent_line, circle_name))
                            print(f"Recorded tangent: IsTangentOfCircle({tangent_line},{circle_name})")
                    elif line.startswith("IsCentreOfCircle("):
                        m = re.match(r'IsCentreOfCircle\((\w+),(\w+)\)', line)
                        if m:
                            point_name, circle_name = m.groups()
                            self.circle_centers[circle_name] = point_name
                    elif line.startswith("Rectangle("):
                        match = re.match(r"Rectangle\((\w+)\)", line)
                        if match:
                            shape_name = match.group(1)
                            # Get all cyclic variations of the rectangle name.
                            variations = get_cyclic_variations_rectangle(shape_name)
                            # Add all these variations to your rectangle set.
                            self.rectangles.update(variations)
                            print(f"Added rectangle variations: {variations}")


                    elif line.startswith("IsDiameterOfCircle("):
                        m = re.match(r'IsDiameterOfCircle\((\w+),(\w+)\)', line)
                        if m:
                            line_name, circle_name = m.groups()
                            self.is_diameter_of_circle.append((line_name, circle_name))
                    elif line.startswith('Parallelogram('):
                        match = re.match(r'Parallelogram\((\w+)\)', line)
                        if match:
                            para_name = match.group(1)
                            print(f"Found parallelogram in TEXT_CDL: {para_name}")
                            self.parallelograms.update(get_cyclic_variations(para_name))
                            print(f"Added parallelogram variations: {self.parallelograms}")
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
                        step_number = parts[0].strip()
                        theorem_part = parts[1].strip()
                        theorem_match = re.search(r'(\w+)\((.*?)\)', theorem_part)

                        if theorem_match:
                            theorem_name = theorem_match.group(1)
                            args = [arg.strip() for arg in theorem_match.group(2).split(',')]

                            # Get premise and conclusion
                            premise = parts[2].strip()
                            conclusions = eval(parts[3].strip())  # This will parse the list string

                            self.theorem_sequence.append({
                                "step_number": step_number,
                                "theorem_name": theorem_name,
                                "args": args,
                                "premise": premise,
                                "conclusions": conclusions
                            })

                            print(f"\nTrying to process theorem: {theorem_name} with:")
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

            if 'GOAL_CDL' in sections:
                goal_line = sections['GOAL_CDL'][0]

                # --- Check for an arc length goal of the form:
                #     Value(LengthOfArc(X))
                arc_length_match = re.search(r'Value\(LengthOfArc\((\w+)\)\)', goal_line)
                if arc_length_match:
                    arc_token = arc_length_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        try:
                            import math
                            expected = float(eval(sections['ANSWER'][0].strip(), {"pi": math.pi, "sqrt": math.sqrt}))
                        except Exception:
                            expected = float(Fraction(sections['ANSWER'][0].strip()))

                        print(f"\nGoal arc length: {arc_token}")
                        print(f"Expected arc length: {expected}")
                        normalized_arc = self.normalize_arc(arc_token)
                        length_var_name = f"lengthArc_{normalized_arc}"
                        arc_length_var = Real(length_var_name)

                        # Check if the constraints are satisfiable
                        if self.solver.check() == sat:
                            # First check if constraints allow the expected value
                            temp_solver1 = Solver()
                            for c in self.solver.assertions():
                                temp_solver1.add(c)

                            # Add constraint that arc_length_var == expected (within epsilon)
                            epsilon = 1e-8
                            temp_solver1.add(
                                And(arc_length_var >= expected - epsilon, arc_length_var <= expected + epsilon))

                            if temp_solver1.check() != sat:
                                print(f"Error: Constraints don't allow the expected arc length {expected}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message="Failed to prove arc length goal: constraints don't allow the expected value.",
                                    details=f"Goal was: LengthOfArc({arc_token}) = {expected}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)
                                return False

                            # Now check if any other value is allowed
                            temp_solver2 = Solver()
                            for c in self.solver.assertions():
                                temp_solver2.add(c)

                            # Add constraint: arc_length_var != expected (outside epsilon range)
                            temp_solver2.add(
                                Or(arc_length_var < expected - epsilon, arc_length_var > expected + epsilon))

                            if temp_solver2.check() == sat:
                                alt_model = temp_solver2.model()
                                alt_value = float(alt_model.eval(arc_length_var).as_decimal(10).rstrip('?'))

                                print(f"Error: The proof doesn't uniquely determine arc length {arc_token}.")
                                print(f"It could be {expected} but also {alt_value}")

                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message="Failed to prove arc length goal: constraints allow multiple values.",
                                    details=f"Goal was: LengthOfArc({arc_token}) = {expected}, but could also be {alt_value}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)
                                return False

                            # Get the computed value from the model
                            model = self.solver.model()
                            calc_expr = model.eval(arc_length_var)
                            val_str = calc_expr.as_decimal(10)
                            if val_str.endswith('?'):
                                val_str = val_str[:-1]
                            calculated_value = float(val_str)

                            print(f"Calculated arc length for {arc_token} is {calculated_value}")
                            print(f"Success: The arc length {arc_token} is uniquely determined to be {expected}.")
                            return True
                        else:
                            print("Solver constraints unsat when verifying arc length goal.")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message="Failed to prove arc length goal: solver is unsatisfiable.",
                                details=f"Goal: LengthOfArc({arc_token}) = {expected}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)
                            return False

                # Add this to the section handling goals in parse_and_verify_proof
                # --- Check for a cosine goal of the form:
                #     Value(Cos(MeasureOfAngle(CBA)))
                # Add this to the section handling goals in parse_and_verify_proof
                # --- Check for a cosine goal of the form:
                #     Value(Cos(MeasureOfAngle(CBA)))
                # --- Check for a cosine goal of the form: Value(Cos(MeasureOfAngle(XXX)))
                cos_match = re.search(r'Value\(Cos\(MeasureOfAngle\((\w+)\)\)\)', goal_line)
                if cos_match:
                    angle_token = cos_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        try:
                            import math
                            expected = float(eval(sections['ANSWER'][0].strip(), {"pi": math.pi, "sqrt": math.sqrt}))
                        except Exception:
                            from fractions import Fraction
                            expected = float(Fraction(sections['ANSWER'][0].strip()))

                        print(f"\nGoal cosine: Cos(MeasureOfAngle({angle_token}))")
                        print(f"Expected value: {expected}")

                        # Create robust fresh solver with only essential constraints
                        fresh_solver = Solver()
                        core_constraints = []

                        # Collect essential constraints only - avoid derived constraints
                        for c in self.solver.assertions():
                            c_str = str(c)
                            # Include basic length, angle constraints, and relationship constraints
                            # But avoid derived constraints for this specific angle
                            if (("length_" in c_str or
                                 "angle_" in c_str or
                                 ">=" in c_str or
                                 "<=" in c_str) and
                                    f"angle_{angle_token} ==" not in c_str):
                                fresh_solver.add(c)
                                core_constraints.append(c)

                        # Get the angle variable
                        angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])

                        # Try using exact values for common angles
                        # Map of exact cos values for common angles
                        special_angles = {
                            0: 1.0,  # cos(0°) = 1
                            60: 0.5,  # cos(60°) = 1/2
                            90: 0.0,  # cos(90°) = 0
                            120: -0.5,  # cos(120°) = -1/2
                            180: -1.0  # cos(180°) = -1
                        }

                        # Check for special angle cases
                        special_angle_match = False
                        for angle_deg, cos_val in special_angles.items():
                            if abs(expected - cos_val) < 1e-10:
                                # Create a temp solver to check if this angle is consistent
                                temp_solver = Solver()
                                for c in core_constraints:
                                    temp_solver.add(c)

                                # Add constraint that angle_var equals this special angle
                                temp_solver.add(angle_var == angle_deg)

                                if temp_solver.check() == sat:
                                    print(
                                        f"Special angle case: {angle_token} could be {angle_deg}° with cos = {cos_val}")

                                    # Check if this is uniquely determined
                                    uniqueness_solver = Solver()
                                    for c in core_constraints:
                                        uniqueness_solver.add(c)

                                    # Try to find a different angle value
                                    epsilon = 0.5  # Use half a degree for angle uniqueness
                                    uniqueness_solver.add(Or(
                                        angle_var < angle_deg - epsilon,
                                        angle_var > angle_deg + epsilon
                                    ))

                                    if uniqueness_solver.check() == unsat:
                                        print(
                                            f"Confirmed: {angle_token} must be exactly {angle_deg}° with cos = {cos_val}")
                                        print(f"Success: cos({angle_token}) = {expected} is verified.")
                                        special_angle_match = True
                                        return True

                        if special_angle_match:
                            # Already verified with special angle case
                            return True

                        # Strategy 1: Direct check for cosine variable
                        cos_var_name = f"cos_{angle_token}"
                        cos_var = None
                        if cos_var_name in self.variables:
                            cos_var = self.variables[cos_var_name]
                            print(f"Found existing cosine variable: {cos_var_name}")

                            # Check if existing cosine variable is consistent with expected value
                            direct_solver = Solver()
                            for c in core_constraints:
                                direct_solver.add(c)

                            # Use a more generous epsilon for floating point comparison
                            epsilon = 1e-6
                            direct_solver.add(And(
                                cos_var >= expected - epsilon,
                                cos_var <= expected + epsilon
                            ))

                            if direct_solver.check() == sat:
                                print(f"Cosine variable {cos_var_name} is consistent with expected value {expected}")

                                # Check uniqueness
                                uniqueness_solver = Solver()
                                for c in core_constraints:
                                    uniqueness_solver.add(c)

                                uniqueness_solver.add(Or(
                                    cos_var < expected - epsilon,
                                    cos_var > expected + epsilon
                                ))

                                if uniqueness_solver.check() == unsat:
                                    print(f"Success: cos({angle_token}) is uniquely determined to be {expected}")
                                    return True
                                else:
                                    alt_model = uniqueness_solver.model()
                                    alt_val = float(alt_model.eval(cos_var).as_decimal(10).rstrip('?'))
                                    print(f"Error: cos({angle_token}) could also be {alt_val}")
                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message="Failed to prove cosine goal: cosine value not uniquely determined.",
                                        details=f"Goal was: Cos(MeasureOfAngle({angle_token})) = {expected}, but could also be {alt_val}"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")
                                    if error.details:
                                        print("Details:", error.details)
                                    return False

                        # Strategy 2: Try to verify from angle value
                        if fresh_solver.check() == sat:
                            model = fresh_solver.model()

                            try:
                                # Get the angle value
                                angle_val_str = model.eval(angle_var).as_decimal(12).rstrip('?')
                                angle_val = float(angle_val_str)
                                print(f"Current angle value from model: {angle_token} = {angle_val}°")

                                # Calculate cosine from this angle
                                theoretical_cos = math.cos(math.radians(angle_val))
                                print(f"Calculated cos({angle_val}°) = {theoretical_cos}")

                                # Check if this matches expected with generous epsilon
                                epsilon = 1e-6
                                if abs(theoretical_cos - expected) < epsilon:
                                    # Check if angle is uniquely determined
                                    uniqueness_solver = Solver()
                                    for c in core_constraints:
                                        uniqueness_solver.add(c)

                                    # Since cosine is even, we need to check for both θ and -θ (or 360-θ)
                                    # For example, cos(30°) = cos(330°)
                                    equivalent_angle = 360 - angle_val
                                    if equivalent_angle == 360:  # Handle the 0° case
                                        equivalent_angle = 0

                                    # Look for a significantly different angle that's not the equivalent angle
                                    angle_epsilon = 0.1  # Use 0.1° for angle uniqueness
                                    uniqueness_solver.add(And(
                                        Or(angle_var < angle_val - angle_epsilon,
                                           angle_var > angle_val + angle_epsilon),
                                        Or(angle_var < equivalent_angle - angle_epsilon,
                                           angle_var > equivalent_angle + angle_epsilon)
                                    ))

                                    if uniqueness_solver.check() == unsat:
                                        print(
                                            f"Success: Angle {angle_token} is constrained to {angle_val}° or {equivalent_angle}°")
                                        print(f"Both give cos({angle_token}) = {expected}, so the goal is verified.")
                                        return True
                                    else:
                                        alt_model = uniqueness_solver.model()
                                        alt_angle = float(alt_model.eval(angle_var).as_decimal(10).rstrip('?'))
                                        alt_cos = math.cos(math.radians(alt_angle))

                                        # If the alternative angle gives the same cosine value, we're still good
                                        if abs(alt_cos - expected) < epsilon:
                                            print(
                                                f"Note: Angle {angle_token} could also be {alt_angle}°, but cos({alt_angle}°) = {alt_cos}")
                                            print(
                                                f"Since all possible angles yield the expected cosine, the goal is verified.")
                                            return True
                                        else:
                                            print(f"Error: Angle {angle_token} could be {angle_val}° or {alt_angle}°")
                                            print(f"Giving cos values {theoretical_cos} and {alt_cos}")
                                            error = GeometricError(
                                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                                message="Failed to prove cosine goal: angle not uniquely determined.",
                                                details=f"Goal was: Cos(MeasureOfAngle({angle_token})) = {expected}"
                                            )
                                            print(f"\nError in {error.tier.name}: {error.message}")
                                            if error.details:
                                                print("Details:", error.details)
                                            return False
                                else:
                                    print(
                                        f"Error: Calculated cosine {theoretical_cos} doesn't match expected {expected}")
                            except Exception as e:
                                print(f"Error calculating cosine from angle value: {e}")

                        # Strategy 3: Try to compute from triangle properties using Law of Cosines
                        print("Trying to verify cosine from triangle properties...")
                        triangle = None

                        # Find a triangle containing the angle vertex
                        for poly in self.polygons:
                            if len(poly) == 3 and angle_token[1] in poly:
                                triangle = poly
                                break

                        if triangle:
                            print(f"Found triangle {triangle} containing angle {angle_token}")

                            # Check if it's a right triangle
                            is_right_triangle = triangle in self.right_triangles
                            if is_right_triangle:
                                print(f"Triangle {triangle} is a right triangle")

                            # Create a fresh solver for triangle calculations
                            triangle_solver = Solver()
                            for c in core_constraints:
                                triangle_solver.add(c)

                            if triangle_solver.check() == sat:
                                model = triangle_solver.model()

                                try:
                                    # Get vertex indices
                                    vertex_idx = triangle.index(angle_token[1])
                                    prev_idx = (vertex_idx - 1) % 3
                                    next_idx = (vertex_idx + 1) % 3

                                    # Get sides - for cosine, we need the two sides adjacent to our angle
                                    side1 = self.add_length(triangle[prev_idx],
                                                            triangle[vertex_idx])  # One adjacent side
                                    side2 = self.add_length(triangle[vertex_idx],
                                                            triangle[next_idx])  # Other adjacent side
                                    opposite = self.add_length(triangle[prev_idx], triangle[next_idx])  # Opposite side

                                    # Get values
                                    side1_val = float(model.eval(side1).as_decimal(10).rstrip('?'))
                                    side2_val = float(model.eval(side2).as_decimal(10).rstrip('?'))
                                    opposite_val = float(model.eval(opposite).as_decimal(10).rstrip('?'))

                                    print(f"Side {triangle[prev_idx]}{triangle[vertex_idx]} = {side1_val}")
                                    print(f"Side {triangle[vertex_idx]}{triangle[next_idx]} = {side2_val}")
                                    print(f"Side {triangle[prev_idx]}{triangle[next_idx]} = {opposite_val}")

                                    # Check if sides are uniquely determined
                                    uniqueness_solver = Solver()
                                    for c in core_constraints:
                                        uniqueness_solver.add(c)

                                    # Use a more generous epsilon for side lengths
                                    epsilon = 1e-6
                                    uniqueness_solver.add(Or(
                                        Or(side1 < side1_val - epsilon, side1 > side1_val + epsilon),
                                        Or(side2 < side2_val - epsilon, side2 > side2_val + epsilon),
                                        Or(opposite < opposite_val - epsilon, opposite > opposite_val + epsilon)
                                    ))

                                    if uniqueness_solver.check() == unsat:
                                        print("Triangle sides are uniquely determined.")

                                        # Calculate cosine using Law of Cosines
                                        # cos(A) = (b² + c² - a²)/(2bc)
                                        # where A is our angle, b & c are adjacent sides, and a is opposite side
                                        if side1_val > 0 and side2_val > 0:  # Ensure no division by zero
                                            cos_val = (side1_val ** 2 + side2_val ** 2 - opposite_val ** 2) / (
                                                        2 * side1_val * side2_val)

                                            # Ensure the value is in valid range for cosine
                                            cos_val = max(-1, min(1, cos_val))

                                            print(f"Calculated cos({angle_token}) = {cos_val} using Law of Cosines")

                                            # Check if calculated value matches expected
                                            # Use more generous epsilon for trig calculations
                                            epsilon = 1e-6
                                            if abs(cos_val - expected) < epsilon:
                                                print(
                                                    f"Success: Calculated cos({angle_token}) = {cos_val} matches expected {expected}")
                                                return True
                                            else:
                                                print(
                                                    f"Error: Calculated cos({angle_token}) = {cos_val} doesn't match expected {expected}")
                                                error = GeometricError(
                                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                                    message="Failed to prove cosine goal: calculated value doesn't match expected.",
                                                    details=f"Goal was: Cos(MeasureOfAngle({angle_token})) = {expected}, calculated: {cos_val}"
                                                )
                                                print(f"\nError in {error.tier.name}: {error.message}")
                                                if error.details:
                                                    print("Details:", error.details)
                                                return False
                                        else:
                                            print("Error: Zero length side(s) in triangle - cannot calculate cosine")
                                    else:
                                        alt_model = uniqueness_solver.model()
                                        print("Error: Triangle sides are not uniquely determined.")
                                        error = GeometricError(
                                            tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                            message="Failed to prove cosine goal: triangle sides not uniquely determined.",
                                            details=f"Goal was: Cos(MeasureOfAngle({angle_token})) = {expected}"
                                        )
                                        print(f"\nError in {error.tier.name}: {error.message}")
                                        if error.details:
                                            print("Details:", error.details)
                                        return False
                                except Exception as e:
                                    print(f"Error calculating cosine from triangle: {e}")
                                    import traceback
                                    traceback.print_exc()
                            else:
                                print("Triangle solver is unsatisfiable")
                        else:
                            print(f"Could not find a triangle containing angle {angle_token}")

                        # Try a brute force approach
                        print("Trying brute force verification...")

                        # Create a direct test solver
                        direct_solver = Solver()
                        for c in core_constraints:
                            direct_solver.add(c)

                        # For cosine, we need to know if the angle can be exactly what we expect
                        # If cos(θ) = 0.5, then θ could be 60° or 300°
                        if -1 <= expected <= 1:  # Valid cosine range
                            possible_angles = []

                            # First angle is arccos(expected) in first quadrant
                            angle1 = math.degrees(math.acos(expected))
                            possible_angles.append(angle1)

                            # Second angle is 360° - arccos(expected) in fourth quadrant
                            angle2 = 360 - angle1
                            possible_angles.append(angle2)

                            print(f"For cos({angle_token}) = {expected}, possible angles: {possible_angles}")

                            # Check if any of these angles are consistent
                            angle_found = False
                            for test_angle in possible_angles:
                                test_solver = Solver()
                                for c in core_constraints:
                                    test_solver.add(c)

                                # Test if this angle value is consistent
                                test_solver.add(angle_var == test_angle)

                                if test_solver.check() == sat:
                                    print(f"Found consistent angle: {angle_token} = {test_angle}°")

                                    # Check if this angle is uniquely determined
                                    uniqueness_solver = Solver()
                                    for c in core_constraints:
                                        uniqueness_solver.add(c)

                                    # Check if there can be a significantly different angle
                                    # that's not one of the expected angles for this cosine
                                    epsilon = 0.5  # Half degree for angle
                                    uniqueness_solver.add(And(
                                        Or(angle_var < angle1 - epsilon or angle_var > angle1 + epsilon),
                                        Or(angle_var < angle2 - epsilon or angle_var > angle2 + epsilon)
                                    ))

                                    if uniqueness_solver.check() == sat:
                                        alt_model = uniqueness_solver.model()
                                        alt_angle = float(alt_model.eval(angle_var).as_decimal(10).rstrip('?'))
                                        alt_cos = math.cos(math.radians(alt_angle))

                                        # If alternative angle gives same cosine, it's still valid
                                        if abs(alt_cos - expected) < 1e-6:
                                            print(f"Note: Angle {angle_token} could also be {alt_angle}°")
                                            print(f"But both give cos({angle_token}) = {expected}")
                                            angle_found = True
                                            break
                                        else:
                                            print(
                                                f"Error: Angle {angle_token} could also be {alt_angle}° with cos = {alt_cos}")
                                            error = GeometricError(
                                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                                message="Failed to prove cosine goal: angle not uniquely constrained to valid values.",
                                                details=f"Goal was: Cos(MeasureOfAngle({angle_token})) = {expected}"
                                            )
                                            print(f"\nError in {error.tier.name}: {error.message}")
                                            if error.details:
                                                print("Details:", error.details)
                                            return False
                                    else:
                                        angle_found = True
                                        print(
                                            f"Success: Angle {angle_token} is constrained to values that give cos({angle_token}) = {expected}")
                                        return True

                            if angle_found:
                                print(f"Success: cos({angle_token}) = {expected} is verified.")
                                return True
                            else:
                                print(f"Error: No angle consistent with cos({angle_token}) = {expected}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message="Failed to prove cosine goal: no consistent angle found.",
                                    details=f"Goal was: Cos(MeasureOfAngle({angle_token})) = {expected}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)
                                return False

                        # If we get here, all strategies failed
                        print(f"Error: Could not verify cos({angle_token}) = {expected} with any strategy")
                        error = GeometricError(
                            tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                            message="Failed to prove cosine goal: all verification strategies failed.",
                            details=f"Goal was: Cos(MeasureOfAngle({angle_token})) = {expected}"
                        )
                        print(f"\nError in {error.tier.name}: {error.message}")
                        if error.details:
                            print("Details:", error.details)
                        return False

                # --- Check for a sine goal of the form:
                #     Value(Sin(MeasureOfAngle(BAC)))
                # --- Check for a sine goal of the form:
                #     Value(Sin(MeasureOfAngle(BAC)))
                # --- Check for a sine goal of the form: Value(Sin(MeasureOfAngle(BAC)))
                # --- Check for a sine goal of the form: Value(Sin(MeasureOfAngle(BAC)))
                sin_match = re.search(r'Value\(Sin\(MeasureOfAngle\((\w+)\)\)\)', goal_line)
                if sin_match:
                    angle_token = sin_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        try:
                            import math
                            expected = float(eval(sections['ANSWER'][0].strip(), {"pi": math.pi, "sqrt": math.sqrt}))
                        except Exception:
                            from fractions import Fraction
                            expected = float(Fraction(sections['ANSWER'][0].strip()))

                        print(f"\nGoal sine: Sin(MeasureOfAngle({angle_token}))")
                        print(f"Expected value: {expected}")

                        # Create a clean solver with only core constraints
                        fresh_solver = Solver()
                        core_constraints = []

                        for c in self.solver.assertions():
                            # Add all constraints to the fresh solver
                            fresh_solver.add(c)
                            core_constraints.append(c)

                        # Get the angle variable
                        angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])

                        # Check if we have a sine variable
                        sin_var_name = f"sin_{angle_token}"
                        sin_var = None
                        if sin_var_name in self.variables:
                            sin_var = self.variables[sin_var_name]
                            print(f"Found existing sine variable: {sin_var_name}")

                        # First check if the sine value is already fully constrained
                        if fresh_solver.check() == sat:
                            model = fresh_solver.model()

                            if sin_var is not None:
                                # Check if sine variable has a unique value
                                temp_solver = Solver()
                                for c in core_constraints:
                                    temp_solver.add(c)

                                # Try to find a different value for sine variable
                                epsilon = 1e-6

                                # Get current value
                                sin_val_expr = model.eval(sin_var)
                                sin_val_str = sin_val_expr.as_decimal(10).rstrip('?')
                                sin_val = float(sin_val_str)

                                print(f"Current sine value: sin({angle_token}) = {sin_val}")

                                # Check uniqueness with a wider range to catch floating point issues
                                # Allow a larger range for potential alternative values
                                temp_solver.add(Or(
                                    sin_var < expected - 0.01,  # Use wider range for testing uniqueness
                                    sin_var > expected + 0.01
                                ))

                                if temp_solver.check() == sat:
                                    alt_model = temp_solver.model()
                                    alt_val = float(alt_model.eval(sin_var).as_decimal(10).rstrip('?'))

                                    if abs(alt_val - expected) > epsilon:
                                        print(f"Error: sin({angle_token}) could also be {alt_val}")

                                        # Try to constrain it further using triangle properties
                                        # First, find a triangle containing this angle
                                        triangle = None
                                        for poly in self.polygons:
                                            if len(poly) == 3 and angle_token[1] in poly:
                                                triangle = poly
                                                break

                                        if triangle:
                                            # Use the triangle to add additional constraints
                                            print(f"Found triangle {triangle} containing angle {angle_token}")

                                            # Check if it's a right triangle
                                            is_right = triangle in self.right_triangles
                                            if is_right:
                                                print(f"Triangle {triangle} is a right triangle")

                                            # Try to constrain the angle based on triangle properties
                                            vertex_idx = triangle.index(angle_token[1])
                                            prev_idx = (vertex_idx - 1) % 3
                                            next_idx = (vertex_idx + 1) % 3

                                            # Get sides related to our angle
                                            adjacent1 = self.add_length(triangle[prev_idx], triangle[vertex_idx])
                                            adjacent2 = self.add_length(triangle[vertex_idx], triangle[next_idx])
                                            opposite = self.add_length(triangle[prev_idx], triangle[next_idx])

                                            # Get values for these sides
                                            adjacent1_val = float(model.eval(adjacent1).as_decimal(10).rstrip('?'))
                                            adjacent2_val = float(model.eval(adjacent2).as_decimal(10).rstrip('?'))
                                            opposite_val = float(model.eval(opposite).as_decimal(10).rstrip('?'))

                                            print(f"Side {triangle[prev_idx]}{triangle[vertex_idx]} = {adjacent1_val}")
                                            print(f"Side {triangle[vertex_idx]}{triangle[next_idx]} = {adjacent2_val}")
                                            print(f"Side {triangle[prev_idx]}{triangle[next_idx]} = {opposite_val}")

                                            # For a right triangle, check which angle we're looking at
                                            if is_right:
                                                # If our angle is the right angle
                                                angle_name = triangle[prev_idx] + angle_token[1] + triangle[next_idx]
                                                normalized = self.normalize_angle_name(angle_name)
                                                right_angle_var = self.add_angle(normalized[0], normalized[1],
                                                                                 normalized[2])
                                                right_angle_val = float(
                                                    model.eval(right_angle_var).as_decimal(10).rstrip('?'))

                                                if abs(right_angle_val - 90) < 1:  # It's the right angle
                                                    # sine of 90° is always 1
                                                    constraint_solver = Solver()
                                                    for c in core_constraints:
                                                        constraint_solver.add(c)

                                                    constraint_solver.add(sin_var == 1.0)

                                                    if constraint_solver.check() == sat:
                                                        print(
                                                            f"Added constraint: sin({angle_token}) = 1.0 (right angle)")
                                                        fresh_solver.add(sin_var == 1.0)
                                                    else:
                                                        print(
                                                            f"Warning: Constraint sin({angle_token}) = 1.0 would make solver unsatisfiable")
                                                else:
                                                    # Find the right angle vertex
                                                    right_angle_vertex = None
                                                    for v_idx in range(3):
                                                        angle_name = triangle[(v_idx - 1) % 3] + triangle[v_idx] + \
                                                                     triangle[(v_idx + 1) % 3]
                                                        angle_var = self.add_angle(angle_name[0], angle_name[1],
                                                                                   angle_name[2])
                                                        angle_val = float(
                                                            model.eval(angle_var).as_decimal(10).rstrip('?'))
                                                        if abs(angle_val - 90) < 1:
                                                            right_angle_vertex = triangle[v_idx]
                                                            break

                                                    if right_angle_vertex:
                                                        # Get hypotenuse (opposite to right angle) and side opposite to our angle
                                                        hyp_vertices = [v for v in triangle if v != right_angle_vertex]
                                                        hyp_side = self.add_length(hyp_vertices[0], hyp_vertices[1])
                                                        hyp_val = float(model.eval(hyp_side).as_decimal(10).rstrip('?'))

                                                        # Find side opposite to our angle
                                                        our_vertex = angle_token[1]
                                                        opposite_vertices = [v for v in triangle if v != our_vertex]
                                                        opp_side = self.add_length(opposite_vertices[0],
                                                                                   opposite_vertices[1])
                                                        opp_val = float(model.eval(opp_side).as_decimal(10).rstrip('?'))

                                                        # sin = opposite/hypotenuse
                                                        computed_sin = opp_val / hyp_val

                                                        # Check if this matches expected
                                                        if abs(computed_sin - expected) < epsilon:
                                                            # Add this constraint to the solver
                                                            constraint_solver = Solver()
                                                            for c in core_constraints:
                                                                constraint_solver.add(c)

                                                            constraint_solver.add(sin_var == computed_sin)

                                                            if constraint_solver.check() == sat:
                                                                print(
                                                                    f"Added constraint: sin({angle_token}) = {computed_sin}")
                                                                fresh_solver.add(sin_var == computed_sin)

                                                                # Check if this now makes the sine value unique
                                                                uniqueness_solver = Solver()
                                                                for c in fresh_solver.assertions():
                                                                    uniqueness_solver.add(c)

                                                                uniqueness_solver.add(Or(
                                                                    sin_var < computed_sin - epsilon,
                                                                    sin_var > computed_sin + epsilon
                                                                ))

                                                                if uniqueness_solver.check() == unsat:
                                                                    print(
                                                                        f"Success: sin({angle_token}) is now uniquely determined to be {computed_sin}")
                                                                    return True
                                                            else:
                                                                print(
                                                                    f"Warning: Constraint sin({angle_token}) = {computed_sin} would make solver unsatisfiable")

                                            # Try Law of Sines
                                            # Find all angles in the triangle
                                            angle_vals = {}
                                            side_vals = {}

                                            for v_idx in range(3):
                                                vertex = triangle[v_idx]
                                                next_vertex = triangle[(v_idx + 1) % 3]
                                                prev_vertex = triangle[(v_idx - 1) % 3]

                                                angle_name = prev_vertex + vertex + next_vertex
                                                side_name = prev_vertex + next_vertex  # Side opposite to this angle

                                                angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])
                                                side_var = self.add_length(side_name[0], side_name[1])

                                                angle_val = float(model.eval(angle_var).as_decimal(10).rstrip('?'))
                                                side_val = float(model.eval(side_var).as_decimal(10).rstrip('?'))

                                                angle_vals[angle_name] = angle_val
                                                side_vals[side_name] = side_val

                                            # Check if any angle/side ratios match our expected sine
                                            for angle_name, angle_val in angle_vals.items():
                                                if angle_name[1] == angle_token[1]:  # This is our angle
                                                    opp_side = angle_name[0] + angle_name[
                                                        2]  # Side opposite to this angle
                                                    if opp_side in side_vals:
                                                        opp_side_val = side_vals[opp_side]

                                                        # For other angles, compute the Law of Sines ratios
                                                        for other_angle, other_val in angle_vals.items():
                                                            if other_angle != angle_name:
                                                                other_opp = other_angle[0] + other_angle[2]
                                                                if other_opp in side_vals:
                                                                    other_opp_val = side_vals[other_opp]

                                                                    # Law of Sines gives us:
                                                                    # sin(A)/a = sin(B)/b = sin(C)/c
                                                                    # So sin(A) = a * sin(B)/b
                                                                    if other_opp_val > 0:
                                                                        other_sin = math.sin(math.radians(other_val))
                                                                        computed_sin = (
                                                                                                   opp_side_val / other_opp_val) * other_sin

                                                                        if abs(computed_sin - expected) < epsilon:
                                                                            print(
                                                                                f"Using Law of Sines: sin({angle_name}) = {computed_sin}")

                                                                            # Add constraint to solver
                                                                            constraint_solver = Solver()
                                                                            for c in core_constraints:
                                                                                constraint_solver.add(c)

                                                                            constraint_solver.add(
                                                                                sin_var == computed_sin)

                                                                            if constraint_solver.check() == sat:
                                                                                print(
                                                                                    f"Added constraint: sin({angle_token}) = {computed_sin}")
                                                                                fresh_solver.add(
                                                                                    sin_var == computed_sin)

                                                                                # Check if this now makes the sine value unique
                                                                                uniqueness_solver = Solver()
                                                                                for c in fresh_solver.assertions():
                                                                                    uniqueness_solver.add(c)

                                                                                uniqueness_solver.add(Or(
                                                                                    sin_var < computed_sin - epsilon,
                                                                                    sin_var > computed_sin + epsilon
                                                                                ))

                                                                                if uniqueness_solver.check() == unsat:
                                                                                    print(
                                                                                        f"Success: sin({angle_token}) is now uniquely determined to be {computed_sin}")
                                                                                    return True
                                                                            else:
                                                                                print(
                                                                                    f"Warning: Constraint sin({angle_token}) = {computed_sin} would make solver unsatisfiable")

                                        # All attempts to constrain failed
                                        error = GeometricError(
                                            tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                            message="Failed to prove sine goal: sine value not uniquely determined.",
                                            details=f"Goal was: Sin(MeasureOfAngle({angle_token})) = {expected}, but could also be {alt_val}"
                                        )
                                        print(f"\nError in {error.tier.name}: {error.message}")
                                        if error.details:
                                            print("Details:", error.details)
                                        return False

                                # If uniqueness check passed, verify the value matches expected
                                if abs(sin_val - expected) < epsilon:
                                    print(f"Success: sin({angle_token}) is uniquely determined to be {expected}")
                                    return True
                                else:
                                    print(f"Error: Unique sine value {sin_val} doesn't match expected {expected}")
                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message="Failed to prove sine goal: calculated value doesn't match expected.",
                                        details=f"Goal was: Sin(MeasureOfAngle({angle_token})) = {expected}, calculated: {sin_val}"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")
                                    if error.details:
                                        print("Details:", error.details)
                                    return False

                            # If no sine variable, try to derive from angle
                            angle_val_str = model.eval(angle_var).as_decimal(10).rstrip('?')
                            angle_val = float(angle_val_str)

                            # Check if angle is uniquely determined
                            temp_solver = Solver()
                            for c in core_constraints:
                                temp_solver.add(c)

                            epsilon = 1e-6
                            temp_solver.add(Or(
                                angle_var < angle_val - epsilon,
                                angle_var > angle_val + epsilon
                            ))

                            if temp_solver.check() == unsat:
                                # Angle is uniquely determined
                                print(f"Angle {angle_token} is uniquely determined to be {angle_val}°")

                                # Calculate sine
                                calc_sin = math.sin(math.radians(angle_val))

                                if abs(calc_sin - expected) < epsilon:
                                    print(
                                        f"Success: Calculated sin({angle_token}) = sin({angle_val}°) = {calc_sin} matches expected {expected}")
                                    return True
                                else:
                                    print(
                                        f"Error: Calculated sin({angle_val}°) = {calc_sin} doesn't match expected {expected}")
                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message="Failed to prove sine goal: calculated value doesn't match expected.",
                                        details=f"Goal was: Sin(MeasureOfAngle({angle_token})) = {expected}, calculated: {calc_sin}"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")
                                    if error.details:
                                        print("Details:", error.details)
                                    return False

                            # If we get here, we need to try all approaches with triangle properties
                            # Finding the triangle and using Law of Sines/Law of Cosines
                            # This part is similar to the logic in the first branch above
                            triangle = None
                            for poly in self.polygons:
                                if len(poly) == 3 and angle_token[1] in poly:
                                    triangle = poly
                                    break

                            if triangle:
                                # Apply triangle analysis similar to above
                                # Calculate sine using Law of Sines or Pythagorean theorem
                                # ... [Logic similar to the first branch]
                                return False
                            else:
                                print(f"Could not find a triangle containing angle {angle_token}")
                                return False
                        else:
                            print("Solver constraints unsat when verifying sine goal.")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message="Failed to prove sine goal: solver is unsatisfiable.",
                                details=f"Goal was: Sin(MeasureOfAngle({angle_token})) = {expected}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)
                            return False




                # --- Check for an arc measure goal of the form:
                #     Value(MeasureOfArc(X))
                arc_match = re.search(r'Value\(MeasureOfArc\((\w+)\)\)', goal_line)
                if arc_match:
                    arc_token = arc_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        try:
                            import math
                            expected = float(eval(sections['ANSWER'][0].strip(), {"pi": math.pi, "sqrt": math.sqrt}))
                        except Exception:
                            expected = float(Fraction(sections['ANSWER'][0].strip()))
                        print(f"\nGoal arc measure: {arc_token}")
                        print(f"Expected arc measure: {expected}")
                        if self.verify_goal_arc(arc_token, expected):
                            return True
                        else:
                            print(f"Error: Could not verify MeasureOfArc({arc_token}) = {expected}")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message=f"Failed to prove arc measure goal: MeasureOfArc({arc_token}) ≠ {expected}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            return False

                quad_area_match = re.search(r'Value\(AreaOfQuadrilateral\((\w+)\)\)', goal_line)
                if quad_area_match:
                    quad_name = quad_area_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        try:
                            import math
                            expected = float(eval(sections['ANSWER'][0].strip(), {"pi": math.pi, "sqrt": math.sqrt}))
                        except Exception:
                            from fractions import Fraction
                            expected = float(Fraction(sections['ANSWER'][0].strip()))

                        print(f"\nGoal quadrilateral area: {quad_name}")
                        print(f"Expected area: {expected}")

                        if quad_name in self.quad_areas:
                            quad_area_var = self.quad_areas[quad_name]
                        else:
                            quad_area_var = Real(f"areaQuadr_{quad_name}")
                            self.quad_areas[quad_name] = quad_area_var

                        if self.solver.check() == sat:
                            # First check if constraints allow the expected value
                            temp_solver1 = Solver()
                            for c in self.solver.assertions():
                                temp_solver1.add(c)

                            # Add constraint that area = expected (within epsilon)
                            epsilon = 1e-8
                            temp_solver1.add(
                                And(quad_area_var >= expected - epsilon, quad_area_var <= expected + epsilon))

                            if temp_solver1.check() != sat:
                                print(f"Error: Constraints don't allow the expected area {expected}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message="Failed to prove quadrilateral area goal: constraints don't allow the expected value.",
                                    details=f"Goal was: AreaOfQuadrilateral({quad_name}) = {expected}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)
                                return False

                            # Now check if any other value is allowed
                            temp_solver2 = Solver()
                            for c in self.solver.assertions():
                                temp_solver2.add(c)

                            # Add constraint: area != expected (outside epsilon range)
                            temp_solver2.add(Or(quad_area_var < expected - epsilon, quad_area_var > expected + epsilon))

                            if temp_solver2.check() == sat:
                                alt_model = temp_solver2.model()
                                alt_value = float(alt_model.eval(quad_area_var).as_decimal(10).rstrip('?'))

                                print(f"Error: The proof doesn't uniquely determine area of {quad_name}.")
                                print(f"It could be {expected} but also {alt_value}")

                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message="Failed to prove quadrilateral area goal: constraints allow multiple values.",
                                    details=f"Goal was: AreaOfQuadrilateral({quad_name}) = {expected}, but could also be {alt_value}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)
                                return False

                            # Get the computed value from the model
                            model = self.solver.model()
                            calc_expr = model.eval(quad_area_var)
                            val_str = calc_expr.as_decimal(10)
                            if val_str.endswith('?'):
                                val_str = val_str[:-1]
                            calculated_value = float(val_str)

                            print(f"Calculated area for {quad_name} is {calculated_value}")
                            print(f"Success: The quadrilateral area is uniquely determined to be {expected}.")
                            return True
                        else:
                            print("Solver constraints unsat when verifying quadrilateral area goal.")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message="Failed to prove quadrilateral area goal: solver is unsatisfiable.",
                                details=f"Goal: AreaOfQuadrilateral({quad_name}) = {expected}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)
                            return False

                # --- Check for a division-of-lengths goal of the form:
                #     Value(Div(LengthOfLine(AF),LengthOfLine(AC)))
                length_div_match = re.search(r'Value\(Div\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)', goal_line)
                if length_div_match:
                    line1 = length_div_match.group(1)
                    line2 = length_div_match.group(2)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        answer_str = sections['ANSWER'][0].strip()
                        try:
                            import math
                            model_answer = float(eval(answer_str, {"pi": math.pi, "sqrt": math.sqrt}))
                        except Exception:
                            model_answer = float(Fraction(answer_str))

                        print(f"\nGoal division of lengths: Div(LengthOfLine({line1}),LengthOfLine({line2}))")
                        print(f"Expected value: {model_answer}")

                        len1 = self.add_length(line1[0], line1[1])
                        len2 = self.add_length(line2[0], line2[1])

                        if self.solver.check() == sat:
                            # First check if the model gives a ratio close to the expected value
                            model = self.solver.model()
                            val1 = model.eval(len1)
                            val2 = model.eval(len2)
                            val1_str = val1.as_decimal(10)
                            if val1_str.endswith('?'):
                                val1_str = val1_str[:-1]
                            val2_str = val2.as_decimal(10)
                            if val2_str.endswith('?'):
                                val2_str = val2_str[:-1]

                            try:
                                float_val1 = float(val1_str)
                                float_val2 = float(val2_str)
                                if float_val2 == 0:
                                    print("Error: Division by zero in length ratio")
                                    return False

                                computed_value = float_val1 / float_val2
                                print(f"Computed division: {computed_value}")

                                epsilon = 1e-8
                                if abs(computed_value - model_answer) >= epsilon:
                                    print(f"Error: Computed division {computed_value} != expected {model_answer}")
                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message="Failed to prove length division goal: computed value doesn't match expected.",
                                        details=f"Goal was: Div(LengthOfLine({line1}),LengthOfLine({line2})) = {model_answer}, computed: {computed_value}"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")
                                    if error.details:
                                        print("Details:", error.details)
                                    return False

                                # Now check if the ratio is uniquely determined
                                temp_solver = Solver()
                                for c in self.solver.assertions():
                                    temp_solver.add(c)

                                # We want to check if there's a model where len1/len2 != model_answer
                                # This is equivalent to len1 != model_answer * len2
                                temp_solver.add(
                                    Or(
                                        len1 < (model_answer - epsilon) * len2,
                                        len1 > (model_answer + epsilon) * len2
                                    )
                                )

                                if temp_solver.check() == sat:
                                    alt_model = temp_solver.model()
                                    alt_val1 = float(alt_model.eval(len1).as_decimal(10).rstrip('?'))
                                    alt_val2 = float(alt_model.eval(len2).as_decimal(10).rstrip('?'))
                                    alt_ratio = alt_val1 / alt_val2 if alt_val2 != 0 else float('inf')

                                    print(f"Error: The proof doesn't uniquely determine the ratio {line1}/{line2}.")
                                    print(f"It could be {computed_value} but also {alt_ratio}")

                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message="Failed to prove length division goal: constraints allow multiple values.",
                                        details=f"Goal was: Div(LengthOfLine({line1}),LengthOfLine({line2})) = {model_answer}, but could also be {alt_ratio}"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")
                                    if error.details:
                                        print("Details:", error.details)
                                    return False

                                print(
                                    f"Success: The length ratio {line1}/{line2} is uniquely determined to be {model_answer}.")
                                return True

                            except Exception as e:
                                print("Error converting length values:", e)
                                return False
                        else:
                            print("Solver constraints unsat when evaluating division-of-lengths goal.")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message="Failed to prove length division goal: solver is unsatisfiable.",
                                details=f"Goal was: Div(LengthOfLine({line1}),LengthOfLine({line2})) = {model_answer}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)
                            return False

                # --- Check for a perimeter goal of the form:
                #     Value(PerimeterOfTriangle(ABC))
                perimeter_match = re.search(r'Value\(PerimeterOfTriangle\((\w+)\)\)', goal_line)
                if perimeter_match:
                    triangle = perimeter_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        import math
                        expected_answer = float(eval(sections['ANSWER'][0].strip(), {"pi": math.pi, "sqrt": math.sqrt}))
                        print(f"\nGoal triangle perimeter: {triangle}")
                        print(f"Expected answer: {expected_answer}")

                        if triangle in self.triangle_perimeters:
                            perimeter_var = self.triangle_perimeters[triangle]
                        else:
                            perimeter_var = self.calculate_perimeter(triangle)

                        if self.solver.check() == sat:
                            # First check if constraints allow the expected value
                            temp_solver1 = Solver()
                            for c in self.solver.assertions():
                                temp_solver1.add(c)

                            # Add constraint that perimeter = expected (within epsilon)
                            epsilon = 1e-8
                            temp_solver1.add(And(perimeter_var >= expected_answer - epsilon,
                                                 perimeter_var <= expected_answer + epsilon))

                            if temp_solver1.check() != sat:
                                print(f"Error: Constraints don't allow the expected perimeter {expected_answer}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message="Failed to prove triangle perimeter goal: constraints don't allow the expected value.",
                                    details=f"Goal was: PerimeterOfTriangle({triangle}) = {expected_answer}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)
                                return False

                            # Now check if any other value is allowed
                            temp_solver2 = Solver()
                            for c in self.solver.assertions():
                                temp_solver2.add(c)

                            # Add constraint: perimeter != expected (outside epsilon range)
                            temp_solver2.add(Or(perimeter_var < expected_answer - epsilon,
                                                perimeter_var > expected_answer + epsilon))

                            if temp_solver2.check() == sat:
                                alt_model = temp_solver2.model()
                                alt_value = float(alt_model.eval(perimeter_var).as_decimal(10).rstrip('?'))

                                print(f"Error: The proof doesn't uniquely determine perimeter of {triangle}.")
                                print(f"It could be {expected_answer} but also {alt_value}")

                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message="Failed to prove triangle perimeter goal: constraints allow multiple values.",
                                    details=f"Goal was: PerimeterOfTriangle({triangle}) = {expected_answer}, but could also be {alt_value}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)
                                return False

                            # Get the computed value from the model
                            model = self.solver.model()
                            calculated_value_str = model.eval(perimeter_var).as_decimal(10)
                            if calculated_value_str.endswith('?'):
                                calculated_value_str = calculated_value_str[:-1]

                            try:
                                calculated_float = float(Fraction(calculated_value_str))
                            except Exception as e:
                                print("Could not convert the calculated perimeter to a float:", e)
                                return False

                            print(f"Calculated perimeter for {triangle} is {calculated_float}")
                            print(f"Success: The triangle perimeter is uniquely determined to be {expected_answer}.")
                            return True
                        else:
                            print("Error: Constraints are unsat (solver.check() == unsat).")
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
                        import math
                        eval_env = {"sqrt": math.sqrt, "pi": math.pi}
                        try:
                            expected_answer = float(eval(answer_str, {"__builtins__": {}}, eval_env))
                        except Exception as e:
                            print("Error evaluating answer expression:", e)
                            return False
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
                            expected_answer = float(Fraction(answer_str))
                        print(f"\nGoal angle: {goal_angle}")
                        print(f"Expected answer: {expected_answer}")
                        success = self.verify_algebraic_goal(goal_angle, expected_answer)
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

                # --- Check for a general goal expression of the form: Value(<expression>)
                general_match = re.search(r'Value\((.+)\)', goal_line)
                if general_match:
                    goal_expr = general_match.group(1).strip()
                    if self.solver.check() == sat:
                        model = self.solver.model()
                        answer_str = sections['ANSWER'][0].strip() if (
                                'ANSWER' in sections and sections['ANSWER']) else None
                        if answer_str is None:
                            print("No answer provided in ANSWER section.")
                            return False

                        # Special handling if goal_expr is of the form Sub(...)
                        if goal_expr.startswith("Sub(") and goal_expr.endswith(")"):
                            inner = goal_expr[4:-1]
                            parts = inner.split(',')
                            if len(parts) == 2:
                                expr1_str = parts[0].strip()
                                expr2_str = parts[1].strip()
                                m1 = re.match(r'AreaOfCircle\((\w+)\)', expr1_str)
                                m2 = re.match(r'AreaOfTriangle\((\w+)\)', expr2_str)
                                if m1 and m2:
                                    circle = m1.group(1)
                                    tri = m2.group(1)
                                    if circle in self.circle_areas and tri in self.triangle_areas:
                                        # Get area variables
                                        circle_area_var = self.circle_areas[circle]
                                        triangle_area_var = self.triangle_areas[tri]

                                        # Get values from the model
                                        area_circle = model.eval(circle_area_var)
                                        area_triangle = model.eval(triangle_area_var)

                                        try:
                                            area_circle_val = float(Fraction(str(area_circle).replace('?', '')))
                                            area_triangle_val = float(Fraction(str(area_triangle).replace('?', '')))
                                        except Exception as e:
                                            print("Error converting area values:", e)
                                            return False

                                        computed_value = area_circle_val - area_triangle_val

                                        try:
                                            import math
                                            model_answer = float(eval(answer_str, {"pi": math.pi, "sqrt": math.sqrt}))
                                        except Exception as e:
                                            model_answer = float(Fraction(answer_str))

                                        epsilon = 1e-8
                                        if abs(computed_value - model_answer) >= epsilon:
                                            print(
                                                f"Error: Computed value {computed_value} != expected {model_answer}")
                                            error = GeometricError(
                                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                                message="Failed to prove goal (Sub form).",
                                                details=f"Computed: {computed_value}, expected: {model_answer}"
                                            )
                                            print(f"\nError in {error.tier.name}: {error.message}")
                                            if error.details:
                                                print("Details:", error.details)
                                            return False

                                        # Check uniqueness - can area difference be something other than model_answer?
                                        temp_solver = Solver()
                                        for c in self.solver.assertions():
                                            temp_solver.add(c)

                                        # Add constraint that sub-expression result must be outside epsilon range of expected
                                        temp_solver.add(
                                            Or(
                                                circle_area_var - triangle_area_var < model_answer - epsilon,
                                                circle_area_var - triangle_area_var > model_answer + epsilon
                                            )
                                        )

                                        if temp_solver.check() == sat:
                                            alt_model = temp_solver.model()
                                            alt_circle = float(
                                                alt_model.eval(circle_area_var).as_decimal(10).rstrip('?'))
                                            alt_triangle = float(
                                                alt_model.eval(triangle_area_var).as_decimal(10).rstrip('?'))
                                            alt_value = alt_circle - alt_triangle

                                            print(
                                                f"Error: The proof doesn't uniquely determine the difference between areas.")
                                            print(f"It could be {computed_value} but also {alt_value}")

                                            error = GeometricError(
                                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                                message="Failed to prove goal (Sub form): constraints allow multiple values.",
                                                details=f"Goal was: Sub({expr1_str},{expr2_str}) = {model_answer}, but could also be {alt_value}"
                                            )
                                            print(f"\nError in {error.tier.name}: {error.message}")
                                            if error.details:
                                                print("Details:", error.details)
                                            return False

                                        print(
                                            "Success: Goal expression (Sub form) matches expected value and is uniquely determined.")
                                        return True

                        # For general expressions, build a mapping for evaluation
                        mapping = {}
                        for var, z3var in self.variables.items():
                            try:
                                val = model.eval(z3var, model_completion=True)
                                val_str = str(val).replace('?', '')
                                mapping[var] = float(Fraction(val_str))
                            except Exception as e:
                                print(f"Error converting free variable {var}: {e}")
                                return False

                        # Also add circle areas and triangle areas if needed
                        for circle, var in self.circle_areas.items():
                            value = model.eval(var)
                            value_str = str(value).replace('?', '')
                            try:
                                mapping[f"ac_{circle.lower()}"] = float(Fraction(value_str))
                            except Exception as e:
                                print("Error converting circle area for", circle, ":", e)
                                return False

                        for tri, var in self.triangle_areas.items():
                            value = model.eval(var)
                            value_str = str(value).replace('?', '')
                            try:
                                mapping[f"at_{tri.lower()}"] = float(Fraction(value_str))
                            except Exception as e:
                                print("Error converting triangle area for", tri, ":", e)
                                return False

                        # Add additional symbols needed for evaluation
                        import math
                        mapping["pi"] = math.pi
                        mapping["sqrt"] = math.sqrt

                        try:
                            computed_value = eval(goal_expr, mapping)
                        except Exception as e:
                            print(f"Error evaluating general goal expression: {e}")
                            return False

                        try:
                            model_answer = float(eval(answer_str, {"pi": math.pi, "sqrt": math.sqrt}))
                        except Exception as e:
                            model_answer = float(Fraction(answer_str))

                        epsilon = 1e-8
                        if abs(computed_value - model_answer) >= epsilon:
                            print(f"Error: Computed general goal value {computed_value} != expected {model_answer}")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message="Failed to prove general goal expression.",
                                details=f"Computed: {computed_value}, expected: {model_answer}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)
                            return False

                        # For general expressions, uniqueness checking is complex
                        # We need to identify which variables influence the goal expression
                        # For simplicity, we'll check if any variable in the mapping can change
                        # while still satisfying all constraints

                        relevant_vars = []
                        for var_name, z3_var in self.variables.items():
                            if var_name in goal_expr:
                                relevant_vars.append((var_name, z3_var))

                        if relevant_vars:
                            # Check if any of the relevant variables can have different values
                            temp_solver = Solver()
                            for c in self.solver.assertions():
                                temp_solver.add(c)

                            # Add constraint that at least one variable must be different
                            var_constraints = []
                            for var_name, z3_var in relevant_vars:
                                current_val = mapping[var_name]
                                var_constraints.append(
                                    Or(z3_var < current_val - epsilon, z3_var > current_val + epsilon)
                                )

                            if var_constraints:
                                temp_solver.add(Or(*var_constraints))

                                if temp_solver.check() == sat:
                                    alt_model = temp_solver.model()

                                    # Build alternative mapping
                                    alt_mapping = mapping.copy()
                                    for var_name, z3_var in relevant_vars:
                                        alt_val = alt_model.eval(z3_var)
                                        alt_val_str = alt_val.as_decimal(10).rstrip('?')
                                        alt_mapping[var_name] = float(Fraction(alt_val_str))

                                    # Evaluate expression with alternative values
                                    try:
                                        alt_value = eval(goal_expr, alt_mapping)

                                        # If the alternative evaluation gives a different value
                                        if abs(alt_value - model_answer) >= epsilon:
                                            print(
                                                f"Error: The proof doesn't uniquely determine the result of {goal_expr}.")
                                            print(f"It could be {computed_value} but could also be {alt_value}")

                                            error = GeometricError(
                                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                                message="Failed to prove general goal: constraints allow multiple values.",
                                                details=f"Goal was: {goal_expr} = {model_answer}, but could also evaluate to {alt_value}"
                                            )
                                            print(f"\nError in {error.tier.name}: {error.message}")
                                            if error.details:
                                                print("Details:", error.details)
                                            return False
                                    except Exception as e:
                                        print(f"Error evaluating alternative: {e}")
                                        # Continue with success if we can't evaluate the alternative

                        print(
                            "Success: General goal expression matches expected value and appears to be uniquely determined.")
                        return True
                    else:
                        print("Solver constraints unsat when evaluating general goal.")
                        error = GeometricError(
                            tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                            message="Failed to prove general goal: solver is unsatisfiable.",
                            details=f"Goal: {goal_expr} = "
                        )
                        print(f"\nError in {error.tier.name}: {error.message}")
                        if error.details:
                            print("Details:", error.details)
                        return False

                print(
                    "Error: Could not parse goal (neither arc length, arc measure, angle, length, perimeter, nor general expression).")
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

    def collect_related_facts(self, goal_points):
        """Collect only facts where ALL points are part of the goal angle"""
        related_facts = {}
        goal_points_set = set(goal_points)

        # 1. Points directly in the goal
        related_facts["Points"] = goal_points

        # 2. Collect lines where ALL points are in goal
        related_lines = []
        for line_name, line_var in self.lengths.items():
            # Extract points from line name (typically in format "length_AB")
            line_points = line_name.split('_')[1] if '_' in line_name else line_name
            line_points_set = set(line_points)
            if line_points_set.issubset(goal_points_set):
                related_lines.append(f"Line {line_points}")
        related_facts["Lines"] = related_lines

        # 3. Collect angles involving ONLY goal points
        related_angles = []
        for angle_name, angle_var in self.angles.items():
            # Extract points from angle name (typically in format "angle_ABC")
            angle_points = angle_name.split('_')[1] if '_' in angle_name else angle_name
            angle_points_set = set(angle_points)
            if angle_points_set.issubset(goal_points_set):
                related_angles.append(f"Angle {angle_points}")
        related_facts["Angles"] = related_angles

        # 4. Collect polygons involving ONLY goal points
        related_polygons = []
        for polygon in self.polygons:
            polygon_set = set(polygon)
            if polygon_set.issubset(goal_points_set):
                related_polygons.append(f"Polygon {polygon}")
        related_facts["Polygons"] = related_polygons

        # 5. Collect collinear facts involving ONLY goal points
        related_collinear = []
        for collinear in self.collinear_facts:
            collinear_set = set(collinear)
            if collinear_set.issubset(goal_points_set):
                related_collinear.append(f"Collinear {''.join(collinear)}")
        related_facts["Collinear Points"] = related_collinear

        # 6. Collect parallel line pairs involving ONLY goal points
        related_parallel = []
        for line1, line2 in self.parallel_pairs:
            if set(line1).issubset(goal_points_set) and set(line2).issubset(goal_points_set):
                related_parallel.append(f"Parallel {line1} and {line2}")
        related_facts["Parallel Lines"] = related_parallel

        # 7. Collect perpendicular line pairs involving ONLY goal points
        related_perp = []
        for line1, line2 in self.perpendicular_pairs:
            if set(line1).issubset(goal_points_set) and set(line2).issubset(goal_points_set):
                related_perp.append(f"Perpendicular {line1} and {line2}")
        related_facts["Perpendicular Lines"] = related_perp

        # 8. Collect circle facts where ALL points are in goal
        related_circles = []
        for circle, center in self.circle_centers.items():
            if circle in goal_points_set and center in goal_points_set:
                related_circles.append(f"Circle {circle} with center {center}")
        related_facts["Circles"] = related_circles

        # 9. Collect cocircular facts involving ONLY goal points
        related_cocircular = []
        for fact in self.cocircular_facts:
            fact_set = set(fact)
            if fact_set.issubset(goal_points_set):
                related_cocircular.append(f"Cocircular {','.join(fact)}")
        related_facts["Cocircular Points"] = related_cocircular

        # 10. Collect right triangles involving ONLY goal points
        related_right_triangles = []
        for triangle in self.right_triangles:
            triangle_set = set(triangle)
            if triangle_set.issubset(goal_points_set):
                related_right_triangles.append(f"Right Triangle {triangle}")
        related_facts["Right Triangles"] = related_right_triangles

        # Remove empty categories
        return {k: v for k, v in related_facts.items() if v}

    def find_related_theorems(self, goal_angle, goal_points):
        """Find only theorems that EXACTLY relate to the goal angle, with no false positives"""
        related_theorems = []
        goal_points_set = set(goal_points)

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if goal angle is directly mentioned in conclusions
            for conclusion in theorem_info["conclusions"]:
                # Check for exact match
                if f"MeasureOfAngle({goal_angle})" in conclusion:
                    is_related = True
                    break

                # Check for possible normalizations of the angle
                # For a goal angle ABC, also check for CBA (normalized form)
                normalized_goal = self.normalize_angle_name(goal_angle)
                angle_matches = re.findall(r'MeasureOfAngle\((\w+)\)', conclusion)
                for angle in angle_matches:
                    normalized_angle = self.normalize_angle_name(angle)
                    if normalized_angle == normalized_goal:
                        is_related = True
                        break

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        return related_theorems

    def generate_goal_analysis_report(self, goal_angle, expected, alt_value):
        """Generate a focused report about why the goal couldn't be uniquely determined"""
        import os
        import datetime

        # Create the directory if it doesn't exist
        output_dir = "/Users/eitan/Desktop/lean/lean_python/info"
        os.makedirs(output_dir, exist_ok=True)

        # Create a timestamped filename
        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"{output_dir}/{self.question_name}_{timestamp}.txt"

        # Extract points involved in the goal angle
        goal_points = list(goal_angle)

        # Get all related facts from our knowledge base
        related_facts = self.collect_related_facts(goal_points)

        # Find theorems that mention the goal or its components
        related_theorems = self.find_related_theorems(goal_angle, goal_points)

        # Write the analysis file
        with open(filename, 'w') as f:
            f.write(f"Analysis Report for {self.question_name}\n")
            f.write("=" * 60 + "\n\n")

            f.write(f"You tried to find the goal angle {goal_angle}\n\n")

            f.write("In the premises you've had:\n")
            f.write("-" * 60 + "\n")
            if related_facts:
                for category, facts in related_facts.items():
                    if facts:  # Only show categories with facts
                        f.write(f"{category}:\n")
                        for fact in facts:
                            f.write(f"  - {fact}\n")
                        f.write("\n")
            else:
                f.write("No facts involving exactly these points " + ", ".join(
                    goal_points) + " were found in the premises.\n\n")

            f.write(f"These are the theorems that have to do with goal {goal_angle} in your proof:\n")
            f.write("-" * 60 + "\n")
            if related_theorems:
                for theorem in related_theorems:
                    f.write(f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n")
                    f.write(f"  Conclusion: {theorem['conclusion']}\n\n")
            else:
                f.write(f"None. Your proof doesn't include any theorems that constrain angle {goal_angle}.\n\n")

            f.write(f"This wasn't enough information to get a unique value for the goal angle {goal_angle}.\n")
            f.write("Your proof allows multiple solutions for this angle.\n")

        print(f"\nDetailed analysis written to: {filename}")
        return filename




    def verify_algebraic_goal(self, goal_angle: str, expected: float, epsilon: float = 1e-8) -> bool:
        print(f"\nVerifying goal angle: {goal_angle}")
        goal_var = self.add_angle(goal_angle[0], goal_angle[1], goal_angle[2])

        if self.solver.check() == sat:
            # First check if constraints allow the expected value
            temp_solver1 = Solver()
            for c in self.solver.assertions():
                temp_solver1.add(c)

            # Add constraint that goal_var == expected (within epsilon)
            temp_solver1.add(And(goal_var >= expected - epsilon, goal_var <= expected + epsilon))

            if temp_solver1.check() != sat:
                print(f"Error: Constraints don't allow the expected angle {expected}")
                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message="Failed to prove angle goal: constraints don't allow the expected value.",
                    details=f"Goal was: MeasureOfAngle({goal_angle}) = {expected}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")
                return False

            # Now check if any other value is allowed
            temp_solver2 = Solver()
            for c in self.solver.assertions():
                temp_solver2.add(c)

            # Add constraint: goal_var != expected (outside epsilon range)
            temp_solver2.add(Or(goal_var < expected - epsilon, goal_var > expected + epsilon))

            if temp_solver2.check() == sat:
                alt_model = temp_solver2.model()
                alt_value = float(alt_model.eval(goal_var).as_decimal(10).rstrip('?'))

                print(f"Error: The proof doesn't uniquely determine angle {goal_angle}.")
                print(f"Multiple solutions exist for this angle.")

                # Collect all relevant information about the goal
                self.generate_goal_analysis_report(goal_angle, expected, alt_value)

                # Still create the error for the regular output flow
                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message="Failed to prove angle goal: constraints allow multiple values.",
                    details=f"Proof analysis saved to info directory"
                )
                print(f"\nError in {error.tier.name}: {error.message}")
                print(f"Details: {error.details}")
                return False

            # If we get here, the constraints uniquely determine the value
            model = self.solver.model()
            val = model.eval(goal_var)
            val_str = val.as_decimal(10)
            if val_str.endswith('?'):
                val_str = val_str[:-1]
            computed = float(val_str)

            print(f"Solver gives {goal_angle} = {computed}°")
            print(f"Success: Angle {goal_angle} is uniquely determined to be {expected}.")
            return True
        else:
            print("Solver is unsat when evaluating goal angle.")
            error = GeometricError(
                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                message="Failed to prove angle goal: solver is unsatisfiable.",
                details=f"Goal was: MeasureOfAngle({goal_angle}) = {expected}"
            )
            print(f"\nError in {error.tier.name}: {error.message}")
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
        """
        Add a length constraint given an algebraic expression.
        For instance, for a TEXT_CDL line like
          Equal(LengthOfLine(JM),5)
        or
          Equal(LengthOfLine(LJ),y)
        this function will create a Z3 variable for the segment (using add_length)
        and then add the equality constraint. It also handles algebraic expressions.
        """
        print(f"\nAdding algebraic length constraint: {line_name} = {expression}")

        # First try to parse the expression as a numeric value.
        try:
            value = float(expression)
            print(f"Adding numeric value for {line_name}: {value}")
            # Use add_length to get the variable (which normalizes the name)
            length_var = self.add_length(line_name[0], line_name[1])
            self.solver.add(length_var == value)
            print(f"Stored numeric value: {line_name} = {value}")
            return
        except ValueError:
            # Not a pure number, so proceed as an algebraic expression.
            pass

        # Extract free variable names from the expression.
        variables = self.extract_variables(expression)
        for var in variables:
            if var not in self.variables:
                self.variables[var] = Real(var)
                print(f"Created new variable for algebraic length: {var}")

        # Get (or create) the length variable using your normalization.
        length_var = self.add_length(line_name[0], line_name[1])
        # Parse the expression into a Z3 expression.
        expr = self.parse_algebraic_expression(expression)
        self.solver.add(length_var == expr)
        print(f"Added constraint: {line_name} == {expr}")

    def check_length_equality(self, line1: str, line2: str) -> bool:
        # Get (or create) the Z3 variables for each segment.
        var1 = self.add_length(line1[0], line1[1])
        var2 = self.add_length(line2[0], line2[1])
        temp_solver = Solver()
        for c in self.solver.assertions():
            temp_solver.add(c)
        # If adding the inequality makes the system unsat, then they are equal.
        temp_solver.add(var1 != var2)
        return temp_solver.check() == unsat

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
            "circle_area_formula",
            "mirror_similar_triangle_judgment_aa",
            "mirror_similar_triangle_property_line_ratio",
            "sine_theorem",
            "tangent_of_circle_property_perpendicular",
            "arc_property_center_angle",
            "arc_property_circumference_angle_external",
            "circle_property_circular_power_segment_and_segment_angle",
            "arc_length_formula",
            "arc_property_circumference_angle_internal",
            "parallel_property_ipsilateral_internal_angle",
            "parallel_property_collinear_extend",
            "midsegment_of_triangle_judgment_parallel",
            "circle_property_chord_perpendicular_bisect_chord",
            "radius_of_circle_property_length_equal",
            "circle_property_circular_power_tangent_and_segment_line",
            "circle_property_circular_power_segment_and_segment_line",
            "rectangle_property_diagonal_equal",
            "parallelogram_property_diagonal_bisection",
            "isosceles_triangle_judgment_line_equal",
            "isosceles_triangle_property_angle_equal",
            "altitude_of_quadrilateral_judgment_left_vertex",
            "parallelogram_property_opposite_line_equal",
            "parallelogram_area_formula_common",
            "altitude_of_quadrilateral_judgment_diagonal",
            "perpendicular_bisector_judgment_distance_equal",
            "cosine_theorem"
        ]

        if theorem_name not in valid_theorems:
            return GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL,
                message=f"Unknown theorem: {theorem_name}",
                details=f"Valid theorems are: {valid_theorems}"
            )








        if theorem_name == "parallelogram_property_opposite_angle_equal":
            version = args[0]
            if version == "1":
                angles_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),\s*MeasureOfAngle\((\w+)\)\)', conclusions[0])
                if angles_match:
                    angle1, angle2 = angles_match.group(1), angles_match.group(2)

                    # Add both angles to solver
                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])
                    self.solver.add(angle1_var == angle2_var)
                    print(f"Added parallelogram opposite angle equality: {angle1} = {angle2}")


            elif version == "2":
                print("2")






        elif theorem_name == "cosine_theorem":

            version = args[0]

            if version == "1":

                # Parse the conclusion to extract sides and angle

                match = re.search(

                    r'Equal\(Add\(Pow\(LengthOfLine\((\w+)\),2\),Mul\(2,LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),Cos\(MeasureOfAngle\((\w+)\)\)\)\),Add\(Pow\(LengthOfLine\(\2\),2\),Pow\(LengthOfLine\(\3\),2\)\)\)',

                    conclusions[0]

                )

                if not match:
                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Invalid conclusion format for cosine_theorem",

                        details=f"Expected cosine theorem format not found in: {conclusions[0]}"

                    )

                side1, side2, side3, angle_str = match.groups()

                # Get (or create) variables for the sides and angle

                side1_var = self.add_length(side1[0], side1[1])

                side2_var = self.add_length(side2[0], side2[1])

                side3_var = self.add_length(side3[0], side3[1])

                angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])

                # First check if the angle already has a unique value

                angle_has_unique_value = False

                angle_value = None

                if self.solver.check() == sat:

                    model = self.solver.model()

                    # Get current angle value from model

                    try:

                        model_angle_val = float(model.eval(angle_var).as_decimal(10).rstrip('?'))

                        # Check if this angle is uniquely determined

                        temp_solver = Solver()

                        for c in self.solver.assertions():
                            temp_solver.add(c)

                        # Try to find a different valid angle value

                        epsilon = 1e-8

                        temp_solver.add(
                            Or(angle_var < model_angle_val - epsilon, angle_var > model_angle_val + epsilon))

                        if temp_solver.check() == unsat:
                            # Angle is uniquely determined!

                            angle_has_unique_value = True

                            angle_value = model_angle_val

                            print(f"Angle {angle_str} already uniquely determined to be {angle_value}°")

                    except Exception as e:

                        print(f"Error checking angle uniqueness: {e}")

                # In the cosine theorem section
                if angle_has_unique_value:
                    # Angle already has a unique value, calculate cosine directly
                    import math
                    cos_val = math.cos(math.radians(angle_value))

                    # Create a sine variable for this angle
                    sin_var_name = f"sin_{angle_str}"
                    if sin_var_name not in self.variables:
                        self.variables[sin_var_name] = Real(sin_var_name)
                        self.solver.add(self.variables[sin_var_name] >= -1)
                        self.solver.add(self.variables[sin_var_name] <= 1)

                    # Add the sine value as well
                    sin_val = math.sin(math.radians(angle_value))

                    # TEST before adding constraints
                    test_solver = Solver()
                    for c in self.solver.assertions():
                        test_solver.add(c)

                    # Test cosine law constraint
                    test_solver.add(
                        side1_var * side1_var ==
                        side2_var * side2_var + side3_var * side3_var -
                        2 * side2_var * side3_var * cos_val
                    )

                    # Only add constraint if it doesn't conflict
                    if test_solver.check() == sat:
                        self.solver.add(
                            side1_var * side1_var ==
                            side2_var * side2_var + side3_var * side3_var -
                            2 * side2_var * side3_var * cos_val
                        )
                        self.solver.add(self.variables[sin_var_name] == sin_val)
                        print(
                            f"Added cosine law constraint with known angle: {side1}^2 = {side2}^2 + {side3}^2 - 2*{side2}*{side3}*{cos_val}")
                        print(f"Added sine value for future reference: sin({angle_str}) = {sin_val}")
                    else:
                        print(
                            f"Warning: Cosine law constraint with value {cos_val} would make solver unsatisfiable - skipping")

                    # Angle already has a unique value, calculate cosine directly

                    import math

                    cos_val = math.cos(math.radians(angle_value))

                    # Add the law of cosines constraint using this numeric cosine value

                    self.solver.add(

                        side1_var * side1_var ==

                        side2_var * side2_var + side3_var * side3_var -

                        2 * side2_var * side3_var * cos_val

                    )

                    print(
                        f"Added cosine law constraint with known angle: {side1}^2 = {side2}^2 + {side3}^2 - 2*{side2}*{side3}*{cos_val}")


                else:

                    # Angle doesn't have a unique value, create cosine variable

                    cos_var_name = f"cos_{angle_str}"

                    if cos_var_name not in self.variables:
                        self.variables[cos_var_name] = Real(cos_var_name)

                    cos_var = self.variables[cos_var_name]

                    # Add constraints: -1 ≤ cos(angle) ≤ 1

                    self.solver.add(cos_var >= -1, cos_var <= 1)

                    # Add the law of cosines constraint using the cosine variable

                    self.solver.add(

                        side1_var * side1_var ==

                        side2_var * side2_var + side3_var * side3_var -

                        2 * side2_var * side3_var * cos_var

                    )

                    print(
                        f"Added cosine law constraint with variable: {side1}^2 = {side2}^2 + {side3}^2 - 2*{side2}*{side3}*cos({angle_str})")

                    # Try to compute sides and derive cosine and angle

                    if self.solver.check() == sat:

                        model = self.solver.model()

                        # Try to get side values from the model

                        try:

                            side1_val = float(model.eval(side1_var).as_decimal(10).rstrip('?'))

                            side2_val = float(model.eval(side2_var).as_decimal(10).rstrip('?'))

                            side3_val = float(model.eval(side3_var).as_decimal(10).rstrip('?'))

                            # Calculate expected cosine value from the sides

                            if side2_val > 0 and side3_val > 0:  # Avoid division by zero

                                expected_cos = (side2_val ** 2 + side3_val ** 2 - side1_val ** 2) / (
                                            2 * side2_val * side3_val)

                                if -1 <= expected_cos <= 1:

                                    # Check if this cosine value is uniquely determined

                                    temp_solver = Solver()

                                    for c in self.solver.assertions():
                                        temp_solver.add(c)

                                    # Try to find a different valid value for the cosine

                                    epsilon = 1e-8

                                    temp_solver.add(
                                        Or(cos_var < expected_cos - epsilon, cos_var > expected_cos + epsilon))

                                    if temp_solver.check() == unsat:
                                        # Cosine is uniquely determined!

                                        self.solver.add(cos_var == expected_cos)

                                        print(f"Added constraint: cos({angle_str}) = {expected_cos}")

                                        # Calculate the angle from cosine

                                        import math

                                        angle_val = math.degrees(math.acos(expected_cos))

                                        # Add the angle constraint

                                        self.solver.add(angle_var == angle_val)

                                        print(f"Added derived angle constraint: {angle_str} = {angle_val}°")

                        except Exception as e:

                            print(f"Error determining angle from sides: {e}")





        elif theorem_name == "altitude_of_quadrilateral_judgment_diagonal":

            # Expected conclusion: ["IsAltitudeOfQuadrilateral(DC,DACB)"]

            altitude_match = re.search(r'IsAltitudeOfQuadrilateral\((\w+),(\w+)\)', conclusions[0])

            if not altitude_match:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Invalid conclusion format for altitude_of_quadrilateral_judgment_diagonal",

                    details="Expected format: IsAltitudeOfQuadrilateral(line,quad)"

                )

            print("Parsing altitude fact...")

            print(f"Full conclusion: {conclusions[0]}")

            line = altitude_match.group(1)  # First capture group (DC)

            quad = altitude_match.group(2)  # Second capture group (DACB)

            print(f"Extracted line: {line}, quad: {quad}")

            # Store the altitude information

            if quad not in self.altitudes:
                self.altitudes[quad] = []

            self.altitudes[quad].append(line)

            # Create a height variable for this quad and link it to the altitude length

            if quad not in self.quad_heights:
                height_var = Real(f"heightQuadr_{quad}")

                self.quad_heights[quad] = height_var

                self.solver.add(height_var >= 0)

                # The height equals the length of the altitude line

                altitude_length = self.add_length(line[0], line[1])

                self.solver.add(height_var == altitude_length)

            print(f"Added altitude fact: {line} is an altitude of {quad} and stored corresponding height")

            return None



        elif theorem_name == "perpendicular_bisector_judgment_distance_equal":

            match = re.search(r'IsPerpendicularBisectorOfLine\((\w+),(\w+)\)', conclusions[0])

            if not match:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Invalid conclusion format for perpendicular_bisector_judgment_distance_equal"

                )

            bisector, bisected = match.groups()  # e.g. "BD", "CA"

            # Find point D from the collinear fact ADC

            bisector_point = None  # This will be point D

            for fact in self.collinear_facts:

                fact_str = ''.join(fact)

                for point in bisector:

                    if point in fact_str and all(p in fact_str for p in bisected):
                        bisector_point = point

                        break

                if bisector_point:
                    break

            if not bisector_point:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Could not find bisector point on the bisected line",

                    details=f"Need collinear fact containing point from {bisector} and points {bisected}"

                )

            # Get the two parts of the bisected line

            parts = [p for p in bisected]

            # Add equal distance constraints for the two parts

            # If bisected is CA and bisector_point is D, this adds CD = DA

            dist1 = self.add_length(bisector_point, parts[0])

            dist2 = self.add_length(bisector_point, parts[1])

            self.solver.add(dist1 == dist2)

            # Add right angle constraints

            # If bisector is BD, get the B point

            other_point = next(p for p in bisector if p != bisector_point)

            # Get collinear points for D (intersecting point)

            collinear_points = None

            for fact in self.collinear_facts:

                if bisector_point in fact:
                    collinear_points = fact

                    break

            if collinear_points:

                # Add right angle for both points on the collinear line

                for p in collinear_points:

                    if p != bisector_point:  # For each endpoint (C and A)

                        angle = self.add_angle(other_point, bisector_point, p)  # BDC and BDA

                        self.solver.add(angle == 90)

                        print(f"Added 90° angle constraint for ∠{other_point}{bisector_point}{p}")

            print(
                f"Added perpendicular bisector constraints: {bisector_point} divides {bisected} equally with right angles")

            return None





        elif theorem_name == "altitude_of_quadrilateral_judgment_left_vertex":
            # Expected conclusion: "IsAltitudeOfQuadrilateral(AE,ACDB)"
            altitude_fact = f"IsAltitudeOfQuadrilateral({args[1].strip()},{args[2].strip()})"
            self.altitudes.add(altitude_fact)
            print(f"Recorded altitude fact: {altitude_fact}")
            return None

        elif theorem_name == "parallelogram_property_opposite_line_equal":
            # Expected conclusion: "Equal(LengthOfLine(DC),LengthOfLine(BA))"
            match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', conclusions[0])
            if match:
                line1, line2 = match.groups()
                var1 = self.add_length(line1[0], line1[1])
                var2 = self.add_length(line2[0], line2[1])
                self.solver.add(var1 == var2)
                print(f"Added constraint: LengthOfLine({line1}) == LengthOfLine({line2})")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Conclusion format error for parallelogram_property_opposite_line_equal."
                )


        elif theorem_name == "parallelogram_area_formula_common":

            # Expected conclusion: "Equal(AreaOfQuadrilateral(ACDB),Mul(HeightOfQuadrilateral(ACDB),LengthOfLine(CD)))"

            match = re.search(

                r'Equal\(AreaOfQuadrilateral\((\w+)\),Mul\(HeightOfQuadrilateral\(\1\),LengthOfLine\((\w+)\)\)\)',

                conclusions[0])

            if match:

                quad, base_line = match.groups()

                # Check that we have a height for this quad

                if quad not in self.quad_heights:
                    return GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"No height established for quadrilateral {quad}",

                        details="Height must be established through an altitude theorem first"

                    )

                # Get or create area variable

                if quad not in self.quad_areas:
                    self.quad_areas[quad] = Real(f"areaQuadr_{quad}")

                    self.solver.add(self.quad_areas[quad] >= 0)

                area_var = self.quad_areas[quad]

                # Get the height variable we previously stored

                height_var = self.quad_heights[quad]

                # Get the base length

                base_var = self.add_length(base_line[0], base_line[1])

                # Add the area formula constraint

                self.solver.add(area_var == height_var * base_var)

                print(
                    f"Added parallelogram area constraint: AreaOfQuadrilateral({quad}) == HeightOfQuadrilateral({quad}) * LengthOfLine({base_line})")

                return None

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Conclusion format error for parallelogram_area_formula_common."

                )




        elif theorem_name == "isosceles_triangle_judgment_line_equal":
            # Expected theorem call: isosceles_triangle_judgment_line_equal(1, T)
            # where T is the triangle name (e.g., "JPN").
            tri = args[1].strip()

            # To record that the triangle is isosceles, add T and all its cyclic rotations
            # to an attribute (e.g. self.isosceles_triangles).
            def cyclic_rotations(s):
                rotations = set()
                for i in range(len(s)):
                    rotations.add(s[i:] + s[:i])
                return rotations

            rotations = cyclic_rotations(tri)
            if not hasattr(self, "isosceles_triangles"):
                self.isosceles_triangles = set()
            self.isosceles_triangles.update(rotations)
            print(f"Recorded isosceles triangle: {tri} and its rotations {rotations}")
            return None



        elif theorem_name == "isosceles_triangle_property_angle_equal":
            # Expected theorem call: isosceles_triangle_property_angle_equal(1, T)
            # where T is a triangle name, e.g., "JPN".
            tri = args[1].strip()
            if len(tri) != 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Triangle name must have exactly 3 letters."
                )
            # For a general triangle T = XYZ, one common convention is to assume the apex is at the first vertex.
            # Then the base angles are at the second and third vertices.
            # We add the constraint: Equal(MeasureOfAngle(XYZ), MeasureOfAngle(YZX))
            # That is, using T's characters: angle1 = add_angle(tri[0], tri[1], tri[2])
            # and angle2 = add_angle(tri[1], tri[2], tri[0])
            angle1 = self.add_angle(tri[0], tri[1], tri[2])
            angle2 = self.add_angle(tri[1], tri[2], tri[0])
            self.solver.add(angle1 == angle2)
            print(f"Added isosceles triangle property: MeasureOfAngle({tri}) == MeasureOfAngle({tri[1:] + tri[0]})")

            # Record the isosceles triangle fact in a general way.
            # Add all cyclic variations of tri into self.isosceles_triangles.
            def cyclic_variations(s):
                return {s[i:] + s[:i] for i in range(len(s))}

            variations = cyclic_variations(tri)
            if not hasattr(self, "isosceles_triangles"):
                self.isosceles_triangles = set()
            self.isosceles_triangles.update(variations)
            print(f"Recorded isosceles triangle: {tri} and rotations: {variations}")
            return None



        elif theorem_name == "arc_length_formula":
            # Expected conclusion, for example:
            # "Equal(LengthOfArc(PSR),Mul(MeasureOfArc(PSR),1/180*pi,RadiusOfCircle(P)))"
            # We use a regex to extract:
            #   - the arc token (e.g. "PSR")
            #   - the multiplier expression (e.g. "1/180*pi")
            #   - the circle identifier (e.g. "P")
            pattern = r'Equal\(LengthOfArc\((\w+)\),Mul\(MeasureOfArc\(\1\),([^,]+),RadiusOfCircle\((\w+)\)\)\)'
            m = re.match(pattern, conclusions[0])
            if m:
                arc_token, factor_expr, circle_id = m.groups()
                # Create a new variable for the arc's length using a naming convention:
                length_var_name = f"lengthArc_{self.normalize_arc(arc_token)}"
                length_arc_var = Real(length_var_name)
                # Retrieve the arc measure variable (stored in self.arcs) using your helper:
                arc_measure = self.add_arc(arc_token)
                try:
                    factor_value = float(eval(factor_expr, {"pi": 3.141592653589793}))
                except Exception as e:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Error evaluating multiplier expression in arc_length_formula",
                        details=str(e)
                    )
                # Get (or create) the radius of the circle:
                if circle_id in self.circle_radii:
                    radius_var = self.circle_radii[circle_id]
                else:
                    radius_var = Real(f"radius_{circle_id}")
                    self.circle_radii[circle_id] = radius_var
                    self.solver.add(radius_var >= 0)
                # Add the constraint:
                # LengthOfArc = MeasureOfArc * factor_value * RadiusOfCircle
                self.solver.add(length_arc_var == arc_measure * factor_value * radius_var)
                print(
                    f"Added arc length constraint: {length_var_name} = {arc_measure} * {factor_value} * RadiusOfCircle({circle_id})")
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Conclusion format error for arc_length_formula",
                    details=f"Expected pattern not found in: {conclusions[0]}"
                )

        elif theorem_name == "circle_property_circular_power_segment_and_segment_line":
            # Expected arguments: version, token1, token2, token3.
            # For example: (1, "AFB", "AGC", "E")
            token1 = args[1].strip()  # e.g., "AFB"
            token2 = args[2].strip()  # e.g., "AGC"
            # token3 (the center "E") is used in the premise but not directly in the conclusion.
            # Interpret token1 = "AFB" as: A, F, B.
            # Then we add the constraint:
            #   (LengthOfLine(AF) * LengthOfLine(AB)) = (LengthOfLine(AG) * LengthOfLine(AC))
            af_var = self.add_length(token1[0], token1[1])  # AF
            ab_var = self.add_length(token1[0], token1[2])  # AB
            # Similarly, for token2 = "AGC" as: A, G, C.
            ag_var = self.add_length(token2[0], token2[1])  # AG
            ac_var = self.add_length(token2[0], token2[2])  # AC
            self.solver.add(af_var * ab_var == ag_var * ac_var)
            print(
                f"Added power-of-a-circle constraint: (LengthOfLine({token1[0]}{token1[1]}) * LengthOfLine({token1[0]}{token1[2]})) = (LengthOfLine({token2[0]}{token2[1]}) * LengthOfLine({token2[0]}{token2[2]}))")
            return None


        elif theorem_name == "circle_property_circular_power_tangent_and_segment_line":
            # Expected arguments: version, token1, token2, token3
            # For example: (1, "DC", "DBF", "E")
            token1 = args[1].strip()  # e.g., "DC"
            token2 = args[2].strip()  # e.g., "DBF"
            # We'll assume token2 has exactly three characters (e.g., "DBF")
            # so that:
            #   external segment = LengthOfLine(DB)  [from token2[0] and token2[1]]
            #   entire secant   = LengthOfLine(DF)  [from token2[0] and token2[2]]
            tangent_var = self.add_length(token1[0], token1[1])  # LengthOfLine(DC)
            external_var = self.add_length(token2[0], token2[1])  # LengthOfLine(DB)
            secant_var = self.add_length(token2[0], token2[2])  # LengthOfLine(DF)
            self.solver.add(tangent_var * tangent_var == external_var * secant_var)
            print(
                f"Added tangent–secant constraint: (LengthOfLine({token1}))² = LengthOfLine({token2[0:2]}) * LengthOfLine({token2[0]}{token2[2]})")
            return None



        elif theorem_name == "rectangle_property_diagonal_equal":
            # Expected argument: the rectangle name (e.g., "PNML")
            if len(args) < 2:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing rectangle name for rectangle_property_diagonal_equal."
                )
            rect = args[1].strip()  # e.g., "PNML"
            if len(rect) < 4:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Rectangle name {rect} is invalid (expected at least 4 letters)."
                )
            # For a rectangle with vertices in cyclic order, the diagonals are:
            #   diag1: from the first vertex to the third, and
            #   diag2: from the second vertex to the fourth.
            diag1 = rect[0] + rect[2]  # e.g., if rect="PNML", diag1 = "PM"
            diag2 = rect[1] + rect[3]  # e.g., diag2 = "NL"
            # Retrieve or create the corresponding length variables.
            var1 = self.add_length(diag1[0], diag1[1])
            var2 = self.add_length(diag2[0], diag2[1])
            # Add the equality constraint.
            self.solver.add(var1 == var2)
            print(f"Added rectangle diagonal equality: LengthOfLine({diag1}) == LengthOfLine({diag2})")
            return None




        elif theorem_name == "parallelogram_property_diagonal_bisection":
            # Expected theorem call: parallelogram_property_diagonal_bisection(1, PNML, J)
            # The intended conclusion is to record that J is the midpoint of the diagonal joining
            # the 1st and 3rd vertices of PNML.
            # In other words, if the diagonal is from P to M (where para_name="PNML"),
            # then we add the constraint: LengthOfLine(PJ) == LengthOfLine(JM).
            if len(args) < 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Insufficient arguments for parallelogram_property_diagonal_bisection."
                )
            para_name = args[1].strip()  # e.g., "PNML"
            mid_candidate = args[2].strip()  # e.g., "J"

            # Compute the first diagonal from the parallelogram: vertices 1 and 3.
            diag = para_name[0] + para_name[2]  # e.g., for "PNML", diag = "PM"
            # To state that mid_candidate J is the midpoint of the diagonal, we require:
            #   LengthOfLine(PJ) = LengthOfLine(JM)
            first_half = self.add_length(para_name[0], mid_candidate)
            second_half = self.add_length(mid_candidate, para_name[2])
            self.solver.add(first_half == second_half)
            print(
                f"Added diagonal bisection: {mid_candidate} is the midpoint of {diag} (LengthOfLine({para_name[0]}{mid_candidate}) == LengthOfLine({mid_candidate}{para_name[2]}))")
            return None






        elif theorem_name == "parallel_property_collinear_extend":

            version = args[0].strip()

            token1 = args[1].strip()  # e.g., "GA"

            token2 = args[2].strip()  # e.g., "HD"

            token3 = args[3].strip()  # e.g., "J"

            # Helper function to add all variations for a given line pair.

            def add_parallel_variations(line_tuple):

                a, b = line_tuple

                variations = {

                    (a, b),

                    (b, a),

                    (a[::-1], b),

                    (a, b[::-1]),

                    (a[::-1], b[::-1]),

                    (b[::-1], a[::-1]),

                    (b, a[::-1]),

                    (b[::-1], a)

                }

                for var in variations:
                    self.parallel_pairs.add(var)

            # For the conclusion, form the new parallel lines.

            if version == "3":

                # For version 3, form new_line1 as token1[0] + token3 and new_line2 as token3 + token1[1]

                new_line1 = token1[0] + token3  # e.g., for token1="GA" and token3="J": "GJ"

                new_line2 = token3 + token1[1]  # e.g., "JA"

            elif version == "1":

                # For version 1, form new_line1 as token3 + token1[0] and new_line2 as token3 + token1[1]

                new_line1 = token3 + token1[0]  # e.g., "JG"

                new_line2 = token3 + token1[1]  # e.g., "JA"

            # Add parallel variations with token2.

            add_parallel_variations((new_line1, token2))

            add_parallel_variations((new_line2, token2))

            print(
                f"[Version {version}] Added parallel extension with new lines: {new_line1} and {new_line2} parallel to {token2}")

            return None







        elif theorem_name == "circle_property_circular_power_segment_and_segment_angle":
            # Expected conclusion: Equal(Sub(MeasureOfArc(BVT),MeasureOfArc(BSU)),Mul(MeasureOfAngle(SRU),2))
            # Use regex to extract the pieces:
            pattern = r'Equal\(Sub\(MeasureOfArc\((\w+)\),MeasureOfArc\((\w+)\)\),Mul\(MeasureOfAngle\((\w+)\),([\d/\.]+)\)\)'
            m = re.match(pattern, conclusions[0])
            if m:
                arc1, arc2, angle_str, factor_str = m.groups()
                arc1_var = self.add_arc(arc1)  # e.g. BVT
                arc2_var = self.add_arc(arc2)  # e.g. BSU
                angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])
                try:
                    factor_val = float(eval(factor_str))
                except Exception:
                    factor_val = 2.0
                # Add the constraint: (arc1 - arc2) == factor * angle
                self.solver.add(arc1_var - arc2_var == factor_val * angle_var)
                print(
                    f"Added constraint: (MeasureOfArc({arc1}) - MeasureOfArc({arc2})) == {factor_val} * MeasureOfAngle({angle_str})")
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Conclusion format error for circle_property_circular_power_segment_and_segment_angle",
                    details=f"Expected pattern not found in: {conclusions[0]}"
                )

        elif theorem_name == "midsegment_of_triangle_judgment_parallel":
            version = args[0]
            if version == "1":
                # (Your version 1 handling here.)
                print("no\n no\n yet")
            elif version == "2":
                # Expected conclusion: ["IsMidsegmentOfTriangle(HD,CFB)"]
                m = re.search(r'IsMidsegmentOfTriangle\((\w+),(\w+)\)', conclusions[0])
                if m:
                    midseg_line, triangle_token = m.groups()
                    # We expect these tokens to match the ones from the theorem call.
                    # For version 2, args[1] should be "HD" and args[2] should be "CFB".
                    if midseg_line != args[1] or triangle_token != args[2]:
                        return GeometricError(
                            tier=ErrorTier.TIER1_THEOREM_CALL,
                            message="Conclusion does not match expected tokens for midsegment_of_triangle_judgment_parallel (version 2)",
                            details=f"Expected IsMidsegmentOfTriangle({args[1]},{args[2]}), got IsMidsegmentOfTriangle({midseg_line},{triangle_token})"
                        )
                    # Optionally, you might also record this fact.
                    self.tangent_facts.add(("IsMidsegmentOfTriangle", (args[1], args[2])))
                    print(
                        f"[Version 2] Added midsegment judgment: IsMidsegmentOfTriangle({midseg_line},{triangle_token})")
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Conclusion format error for midsegment_of_triangle_judgment_parallel (version 2)",
                        details="Expected format: IsMidsegmentOfTriangle(HD,CFB)"
                    )




        elif theorem_name == "arc_property_circumference_angle_internal":
            # Expected conclusion:
            # Equal(MeasureOfAngle(BCD),Sub(180,Mul(MeasureOfArc(OBD),1/2)))
            #
            # We'll extract:
            #   - the inscribed angle token (e.g. "BCD")
            #   - the arc token (e.g. "OBD")
            #   - the factor expression (e.g. "1/2")
            pattern = r'Equal\(MeasureOfAngle\((\w{3})\),Sub\(180,Mul\(MeasureOfArc\((\w+)\),([^,)]+)\)\)\)'
            m = re.match(pattern, conclusions[0])
            if m:
                angle_token, arc_token, factor_expr = m.groups()
                # Get the angle variable (using your helper, which normalizes the three-letter string)
                angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])
                # Get the arc measure variable (using your add_arc method)
                arc_var = self.add_arc(arc_token)
                try:
                    factor_value = float(eval(factor_expr, {"pi": 3.141592653589793}))
                except Exception as e:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Error evaluating multiplier expression in arc_property_circumference_angle_internal",
                        details=str(e)
                    )
                # Add the constraint:
                #   MeasureOfAngle(angle_token) = 180 - (factor_value * MeasureOfArc(arc_token))
                self.solver.add(angle_var == 180 - (arc_var * factor_value))
                print(
                    f"Added arc circumference internal angle constraint: MeasureOfAngle({angle_token}) = 180 - {factor_value} * MeasureOfArc({arc_token})")
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Conclusion format error for arc_property_circumference_angle_internal",
                    details=f"Expected pattern not found in: {conclusions[0]}"
                )







        elif theorem_name == "circle_property_chord_perpendicular_bisect_chord":

            # Expecting arguments: [version, circle_token, bisector_line, chord_token]

            if len(args) < 4:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Missing arguments for circle_property_chord_perpendicular_bisect_chord",

                    details="Expected format: circle_property_chord_perpendicular_bisect_chord(1, <circle>, <bisector_line>, <chord>)"

                )

            circle_token = args[1].strip()  # e.g., "O"

            bisector_line = args[2].strip()  # e.g., "OP"

            chord_token = args[3].strip()  # e.g., "BC"

            # Record the fact for later use.

            if not hasattr(self, "bisector_facts"):
                self.bisector_facts = set()

            self.bisector_facts.add((bisector_line, chord_token))

            print(f"Recorded fact: {bisector_line} is the perpendicular bisector of {chord_token}")

            # Look for a collinearity fact that shows both endpoints of the chord are collinear with a third point.

            # For example, if chord_token is "BC" and a collinearity fact "Collinear(BPC)" exists,

            # then the extra point "P" is our candidate midpoint.

            midpoint = None

            for fact in self.collinear_facts:

                # fact is a list of points (e.g., ['B','P','C'])

                if set(chord_token).issubset(set(fact)):

                    extras = [pt for pt in fact if pt not in chord_token]

                    if extras:
                        midpoint = extras[0]

                        break

            if midpoint is not None:

                print(f"Found candidate midpoint for chord {chord_token}: {midpoint}")

                # Check that the bisector line passes through this midpoint.

                if midpoint in bisector_line:

                    # Identify the other endpoint of the bisector line.

                    other_bisector = None

                    for pt in bisector_line:

                        if pt != midpoint:
                            other_bisector = pt

                            break

                    if other_bisector is not None:

                        # Add perpendicular constraints on both "sides" of the chord.

                        angle1 = self.add_angle(chord_token[0], midpoint, other_bisector)

                        angle2 = self.add_angle(other_bisector, midpoint, chord_token[1])

                        self.solver.add(angle1 == 90, angle2 == 90)

                        print(
                            f"Added perpendicular constraints: angle({chord_token[0]}{midpoint}{other_bisector}) and angle({other_bisector}{midpoint}{chord_token[1]}) are both 90°")

                        # **New step:** Also add the bisection constraint: the chord is divided equally.

                        len_first = self.add_length(chord_token[0], midpoint)

                        len_second = self.add_length(midpoint, chord_token[1])

                        self.solver.add(len_first == len_second)

                        print(
                            f"Added chord bisection constraint: LengthOfLine({chord_token[0]}{midpoint}) == LengthOfLine({midpoint}{chord_token[1]})")

                    else:

                        print(f"Could not determine the other endpoint of bisector {bisector_line}.")

                else:

                    print(
                        f"Midpoint {midpoint} is not on the bisector line {bisector_line}; cannot add perpendicular constraint.")

            else:

                print(
                    f"No collinear fact found that identifies a midpoint for chord {chord_token}; cannot add perpendicular constraint.")






        elif theorem_name == "radius_of_circle_property_length_equal":
            # Expecting arguments: [version, line_token, circle_token] e.g., ("1", "OA", "O")
            if len(args) < 3:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Missing arguments for radius_of_circle_property_length_equal",
                    details="Expected format: radius_of_circle_property_length_equal(1, <line>, <circle>)"
                )
            line_token = args[1].strip()  # e.g., "OA"
            circle_token = args[2].strip()  # e.g., "O"
            # Ensure that a radius variable exists for the circle.
            if circle_token not in self.circle_radii:
                radius_var = Real(f"radius_{circle_token}")
                self.circle_radii[circle_token] = radius_var
                self.solver.add(radius_var >= 0)
            else:
                radius_var = self.circle_radii[circle_token]
            # Get (or create) the length variable for the given line.
            length_var = self.add_length(line_token[0], line_token[1])
            # Add the constraint that the line’s length equals the circle’s radius.
            self.solver.add(length_var == radius_var)
            print(f"Added radius property: LengthOfLine({line_token}) = RadiusOfCircle({circle_token})")


        elif theorem_name == "parallel_property_ipsilateral_internal_angle":
            # Expected conclusion: Equal(Add(MeasureOfAngle(BAD),MeasureOfAngle(ADC)),180)
            # We use a regex to capture the two angle tokens.
            pattern = r'Equal\(Add\(MeasureOfAngle\((\w{3})\),MeasureOfAngle\((\w{3})\)\),180\)'
            m = re.match(pattern, conclusions[0])
            if m:
                angle1_token, angle2_token = m.groups()  # e.g. "BAD" and "ADC"
                # Create the corresponding Z3 variables for these angles using your helper.
                angle1_var = self.add_angle(angle1_token[0], angle1_token[1], angle1_token[2])
                angle2_var = self.add_angle(angle2_token[0], angle2_token[1], angle2_token[2])
                # Add the constraint that their sum equals 180.
                self.solver.add(angle1_var + angle2_var == 180)
                print(f"Added ipsilateral internal angle constraint: {angle1_token} + {angle2_token} = 180")
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Conclusion format error for parallel_property_ipsilateral_internal_angle",
                    details=f"Expected pattern not found in: {conclusions[0]}"
                )


        elif theorem_name == "tangent_of_circle_property_perpendicular":

            version = args[0]

            if version == "1":

                tangent_line = args[1]  # e.g., "AM"

                center = args[2]  # e.g., "O"

                # For version 1, assume tangent_line is [external point][tangency point]

                tangency_point = tangent_line[1]

                tangent_other = tangent_line[0]

                angle_name = tangent_other + tangency_point + center  # e.g., "AMO"

                normalized_angle = self.normalize_angle_name(angle_name)

                angle_var = self.add_angle(normalized_angle[0], normalized_angle[1], normalized_angle[2])

                self.solver.add(angle_var == 90)

                print(
                    f"[Version 1] Added tangent perpendicular constraint: {tangent_line} ⟂ {center}{tangency_point} (angle {normalized_angle} = 90)")

            elif version == "2":

                tangent_line = args[1]  # e.g., "AN"

                center = args[2]  # e.g., "O"

                tangency_point = tangent_line[1]

                tangent_other = tangent_line[0]

                # For version 2, we might define the angle in a different order:

                angle_name = center + tangency_point + tangent_other  # e.g., "ONA"

                normalized_angle = self.normalize_angle_name(angle_name)

                angle_var = self.add_angle(normalized_angle[0], normalized_angle[1], normalized_angle[2])

                self.solver.add(angle_var == 90)

                print(
                    f"[Version 2] Added tangent perpendicular constraint: {tangent_line} ⟂ {center}{tangency_point} (angle {normalized_angle} = 90)")

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message=f"Unsupported version {version} for tangent_of_circle_property_perpendicular"

                )






        elif theorem_name == "arc_property_center_angle":

            version = args[0]

            if version == "1":

                arc_name = args[1]  # e.g., "OMN"

                center = args[2]  # e.g., "O"

                arc_var = self.add_arc(arc_name)

                # Expected conclusion: "Equal(MeasureOfArc(OMN),MeasureOfAngle(NOM))"

                pattern = r'Equal\(MeasureOfArc\(' + re.escape(arc_name) + r'\),MeasureOfAngle\((\w{3})\)\)'

                m = re.search(pattern, conclusions[0])

                if m:

                    angle_str = m.group(1)  # e.g., "NOM"

                    angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])

                    self.solver.add(arc_var == angle_var)

                    print(f"Added arc center angle constraint: MeasureOfArc({arc_name}) == MeasureOfAngle({angle_str})")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Conclusion format error for arc_property_center_angle",

                        details=f"Expected pattern Equal(MeasureOfArc({arc_name}),MeasureOfAngle(XXX)) but got {conclusions[0]}"

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message=f"Version {version} for arc_property_center_angle not implemented"

                )









        elif theorem_name == "arc_property_circumference_angle_external":

            version = args[0]

            if version == "1":

                arc_name = args[1]  # e.g., "OMN"

                external_point = args[2]  # e.g., "B"

                arc_var = self.add_arc(arc_name)

                # Expected conclusion: "Equal(MeasureOfAngle(NBM),Mul(MeasureOfArc(OMN),1/2))"

                pattern = r'Equal\(MeasureOfAngle\((\w{3})\),Mul\(MeasureOfArc\(' + re.escape(arc_name) + r'\),1/2\)\)'

                m = re.search(pattern, conclusions[0])

                if m:

                    angle_str = m.group(1)  # e.g., "NBM"

                    angle_var = self.add_angle(angle_str[0], angle_str[1], angle_str[2])

                    from fractions import Fraction

                    self.solver.add(angle_var == arc_var * Fraction(1, 2))

                    print(
                        f"Added arc circumference external angle constraint: MeasureOfAngle({angle_str}) == 1/2 * MeasureOfArc({arc_name})")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Conclusion format error for arc_property_circumference_angle_external",

                        details=f"Expected pattern Equal(MeasureOfAngle(XXX),Mul(MeasureOfArc({arc_name}),1/2)) but got {conclusions[0]}"

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message=f"Version {version} for arc_property_circumference_angle_external not implemented"

                )





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



        elif theorem_name == "mirror_similar_triangle_judgment_aa":
            match = re.search(r'MirrorSimilarBetweenTriangle\((\w+),(\w+)\)', conclusions[0])
            if match:
                tri1, tri2 = match.groups()
                print(f"Adding mirror similarity: {tri1} and {tri2} are mirror similar by AA.")
                self.add_mirror_similar_triangles(tri1, tri2)
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Conclusion format error for mirror_similar_triangle_judgment_aa",
                    details=f"Expected format: MirrorSimilarBetweenTriangle(XXX,YYY) but got {conclusions[0]}"
                )







        elif theorem_name == "sine_theorem":

            # Expected conclusion pattern:

            # Equal(Mul(LengthOfLine(AB),Sin(MeasureOfAngle(ABC))),

            #       Mul(LengthOfLine(AC),Sin(MeasureOfAngle(BCA))))

            pattern = r'Equal\(Mul\(LengthOfLine\((\w{2})\),Sin\(MeasureOfAngle\((\w{3})\)\)\),Mul\(LengthOfLine\((\w{2})\),Sin\(MeasureOfAngle\((\w{3})\)\)\)\)'

            match = re.search(pattern, conclusions[0])

            import math

            if match:

                side1, angle1_str, side2, angle2_str = match.groups()

                # Get (or create) the Z3 variables for the segments and angles

                length1_var = self.add_length(side1[0], side1[1])

                length2_var = self.add_length(side2[0], side2[1])

                angle1_var = self.add_angle(angle1_str[0], angle1_str[1], angle1_str[2])

                angle2_var = self.add_angle(angle2_str[0], angle2_str[1], angle2_str[2])

                # Create or get sine variables for both angles

                sin1_var_name = f"sin_{angle1_str}"

                sin2_var_name = f"sin_{angle2_str}"

                if sin1_var_name not in self.variables:
                    self.variables[sin1_var_name] = Real(sin1_var_name)

                    self.solver.add(self.variables[sin1_var_name] >= 0)

                    self.solver.add(self.variables[sin1_var_name] <= 1)

                if sin2_var_name not in self.variables:
                    self.variables[sin2_var_name] = Real(sin2_var_name)

                    self.solver.add(self.variables[sin2_var_name] >= 0)

                    self.solver.add(self.variables[sin2_var_name] <= 1)

                sin1_var = self.variables[sin1_var_name]

                sin2_var = self.variables[sin2_var_name]

                # Check if the angles have unique values

                unique_angles = True

                angle1_val = None

                angle2_val = None

                if self.solver.check() == sat:

                    model = self.solver.model()

                    # Check if angle1 has a unique value

                    try:

                        a1_val_str = model.eval(angle1_var).as_decimal(10)

                        if a1_val_str.endswith('?'):
                            a1_val_str = a1_val_str[:-1]

                        angle1_val = float(a1_val_str)

                        # Check if angle2 has a unique value

                        a2_val_str = model.eval(angle2_var).as_decimal(10)

                        if a2_val_str.endswith('?'):
                            a2_val_str = a2_val_str[:-1]

                        angle2_val = float(a2_val_str)

                        # Check uniqueness with temporary solvers

                        temp_solver1 = Solver()

                        for c in self.solver.assertions():
                            temp_solver1.add(c)

                        epsilon = 1e-6

                        temp_solver1.add(Or(

                            angle1_var < angle1_val - epsilon,

                            angle1_var > angle1_val + epsilon

                        ))

                        temp_solver2 = Solver()

                        for c in self.solver.assertions():
                            temp_solver2.add(c)

                        temp_solver2.add(Or(

                            angle2_var < angle2_val - epsilon,

                            angle2_var > angle2_val + epsilon

                        ))

                        if temp_solver1.check() == sat or temp_solver2.check() == sat:
                            # At least one angle doesn't have a unique value

                            unique_angles = False


                    except Exception as e:

                        print(f"Error evaluating angles: {e}")

                        unique_angles = False

                    if unique_angles:

                        # Both angles have unique values, calculate sines

                        sin1 = math.sin(math.radians(angle1_val))

                        sin2 = math.sin(math.radians(angle2_val))

                        # Add sine values to variables

                        self.solver.add(sin1_var == sin1)

                        self.solver.add(sin2_var == sin2)

                        # IMPORTANT: CORRECT LAW OF SINES CONSTRAINT

                        # In Law of Sines, we need to pair each angle with the OPPOSITE side

                        # To identify the opposite sides, we need to analyze the triangle

                        # Determine the triangle from the angles

                        # The first angle (angle1_str) is at vertex angle1_str[1]

                        # The second angle (angle2_str) is at vertex angle2_str[1]

                        # Find the triangle containing both vertices

                        triangle = None

                        for poly in self.polygons:

                            if len(poly) == 3 and angle1_str[1] in poly and angle2_str[1] in poly:
                                triangle = poly

                                break

                        if triangle:

                            # Now determine which sides are opposite to which angles

                            # For an angle at vertex X, the opposite side is the side not containing X

                            # Get vertices not in angle1/angle2

                            other_vertex = next(v for v in triangle if v != angle1_str[1] and v != angle2_str[1])

                            # The side opposite to angle1_str is between angle2_str[1] and other_vertex

                            opposite_side1 = self.add_length(angle2_str[1], other_vertex)

                            # The side opposite to angle2_str is between angle1_str[1] and other_vertex

                            opposite_side2 = self.add_length(angle1_str[1], other_vertex)

                            # Apply the correctly paired Law of Sines constraint

                            self.solver.add(sin1_var * opposite_side2 == sin2_var * opposite_side1)

                            print(f"Added sine theorem constraint with known angles: "

                                  f"sin({angle1_str})={sin1} * opposite_side2 = sin({angle2_str})={sin2} * opposite_side1")

                        else:

                            # If we can't determine the triangle, use a more general constraint

                            # Try both possible pairings and see which one is consistent

                            # Original constraint from code

                            self.solver.add(length1_var * sin2 == length2_var * sin1)

                            print(f"Added sine theorem constraint: {side1} * {sin2} = {side2} * {sin1}")

                    else:

                        # At least one angle doesn't have unique value, use variables

                        # Use a more general constraint since we can't determine the exact triangle structure

                        # This will apply the Law of Sines with the sides and angles as matched in the conclusion

                        self.solver.add(length1_var * sin2_var == length2_var * sin1_var)

                        print(
                            f"Added sine theorem constraint with variables: {side1} * sin({angle2_str}) = {side2} * sin({angle1_str})")

                        # Try to solve for the sine values if possible

                        if self.solver.check() == sat:
                            updated_model = self.solver.model()

                            # See if we can derive unique values for the sines

                            sin1_val_updated = updated_model.eval(sin1_var)

                            sin2_val_updated = updated_model.eval(sin2_var)

                            print(
                                f"Updated sine values: sin({angle1_str}) = {sin1_val_updated}, sin({angle2_str}) = {sin2_val_updated}")

                            # Try to derive angles if sines are uniquely determined

                            # This part would be similar to the previous implementation checking for uniqueness

                            # and deriving angles when possible

                else:

                    # If solver is not satisfiable, return an error

                    return GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message="Solver unsat when trying to evaluate angles for sine theorem"

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Conclusion format error for sine_theorem",

                    details=f"Expected pattern Equal(Mul(LengthOfLine(XX),Sin(MeasureOfAngle(XXX))),Mul(LengthOfLine(XX),Sin(MeasureOfAngle(XXX)))) but got {conclusions[0]}"

                )






        elif theorem_name == "mirror_similar_triangle_property_line_ratio":
            match = re.search(
                r'Equal\(LengthOfLine\((\w+)\),Mul\(LengthOfLine\((\w+)\),RatioOfMirrorSimilarTriangle\((\w+),(\w+)\)\)\)',
                conclusions[0]
            )
            if match:
                line1, line2, tri1, tri2 = match.groups()
                norm_tris = self.canonicalize_mirror_triangle_pair(tri1, tri2)
                if not norm_tris:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message=f"Invalid triangle names in mirror_similar_triangle_property_line_ratio: {tri1}, {tri2}"
                    )
                if norm_tris not in self.mirror_triangle_ratios:
                    var_name = f"ratio_mirror_{norm_tris[0]}_{norm_tris[1]}"
                    self.mirror_triangle_ratios[norm_tris] = Real(var_name)
                ratio = self.mirror_triangle_ratios[norm_tris]
                line1_var = self.add_length(line1[0], line1[1])
                line2_var = self.add_length(line2[0], line2[1])
                self.solver.add(line1_var == line2_var * ratio)
                print(
                    f"Added mirror similar triangle ratio constraint: LengthOfLine({line1}) = LengthOfLine({line2}) * RatioOfMirrorSimilarTriangle({tri1},{tri2})")
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Conclusion format error for mirror_similar_triangle_property_line_ratio",
                    details=f"Expected format: Equal(LengthOfLine(XXX),Mul(LengthOfLine(YYY),RatioOfMirrorSimilarTriangle(ZZZ,WWW))) but got {conclusions[0]}"
                )





        elif theorem_name == "triangle_area_formula_sine":

            # Expected conclusion format (for example):

            # "Equal(AreaOfTriangle(CAB),Mul(LengthOfLine(CA),LengthOfLine(CB),Sin(MeasureOfAngle(BCA)),1/2))"

            c = conclusions[0]

            pat = r"Equal\(AreaOfTriangle\((\w+)\),Mul\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),Sin\(MeasureOfAngle\((\w{3})\)\),([\d/\.]+)\)\)"

            mm = re.match(pat, c)

            if mm:

                tri_name, side1, side2, angle_name, factor_str = mm.groups()

                # Ensure an area variable exists for the triangle.

                if tri_name not in self.triangle_areas:
                    self.triangle_areas[tri_name] = Real(f"areaTriangle_{tri_name}")

                    self.solver.add(self.triangle_areas[tri_name] >= 0)

                area_var = self.triangle_areas[tri_name]

                # Get the side length variables.

                side1_var = self.add_length(side1[0], side1[1])

                side2_var = self.add_length(side2[0], side2[1])

                # Get the angle variable.

                angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

                # Convert the factor (e.g. "1/2") to a float.

                try:

                    factor_value = float(eval(factor_str))

                except Exception as e:

                    print(f"Error evaluating factor {factor_str}: {e}. Defaulting to 0.5.")

                    factor_value = 0.5

                # Try to evaluate the angle numerically so we can compute its sine.

                if self.solver.check() == sat:

                    model = self.solver.model()

                    # Use model_completion=True in case the angle variable has a default value.

                    a_val_str = model.eval(angle_var, model_completion=True).as_decimal(10)

                    if a_val_str.endswith('?'):
                        a_val_str = a_val_str[:-1]

                    try:

                        from fractions import Fraction

                        angle_val = float(Fraction(a_val_str))

                    except Exception as e:

                        return GeometricError(

                            tier=ErrorTier.TIER2_PREMISE,

                            message="Cannot convert angle value to float in triangle_area_formula_sine step",

                            details=str(e)

                        )

                    import math

                    # Compute the sine (note: math.sin expects radians).

                    sin_val = round(math.sin(math.radians(angle_val)), 10)

                    # Now add the constraint with the computed sine value.

                    self.solver.add(area_var == factor_value * side1_var * side2_var * sin_val)

                    print(
                        f"[triangle_area_formula_sine] Added constraint: AreaOfTriangle({tri_name}) = {factor_value} * LengthOfLine({side1}) * LengthOfLine({side2}) * {sin_val}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message="Solver unsat when evaluating angle for triangle_area_formula_sine",

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Conclusion format error for triangle_area_formula_sine",

                    details=f"Expected pattern Equal(AreaOfTriangle(XXX),Mul(LengthOfLine(YY),LengthOfLine(ZZ),Sin(MeasureOfAngle(AAA)),factor)) but got {conclusions[0]}"

                )




        elif theorem_name == "right_triangle_judgment_angle":
            # Expecting a theorem call like: right_triangle_judgment_angle(1,GHE)
            # and a conclusion list like: ["RightTriangle(GHE)"]
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing triangle argument for right_triangle_judgment_angle",
                        details="Expected right_triangle_judgment_angle(1, triangle)"
                    )
                triangle = args[1].strip()
                # Call the helper to mark this triangle as a right triangle.
                # This method adds the constraint that the angle (using the first point as vertex)
                # is equal to 90.
                self.add_right_triangle(triangle)
                print(f"Added right triangle judgment: {triangle} is a right triangle (angle = 90).")
            elif version == "2":
                print("2")





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

            # Expecting: "Equal(AreaOfCircle(D),Mul(pi,RadiusOfCircle(D),RadiusOfCircle(D)))"

            c = conclusions[0]

            mm = re.match(r'Equal\(AreaOfCircle\((\w+)\),Mul\(pi,RadiusOfCircle\((\w+)\),RadiusOfCircle\(\2\)\)\)', c)

            if mm:

                circle_area, circle_rad = mm.groups()

                if circle_area not in self.circle_areas:
                    self.circle_areas[circle_area] = Real(f"area_{circle_area}")

                    self.solver.add(self.circle_areas[circle_area] >= 0)

                if circle_rad not in self.circle_radii:
                    self.circle_radii[circle_rad] = Real(f"radius_{circle_rad}")

                    self.solver.add(self.circle_radii[circle_rad] >= 0)

                Avar = self.circle_areas[circle_area]

                Rvar = self.circle_radii[circle_rad]

                # Use the symbolic pi_sym instead of a numerical value.

                self.solver.add(Avar == self.pi * (Rvar * Rvar))

                print(f"circle_area_formula => area_{circle_area} = pi * radius_{circle_rad}^2")





        elif theorem_name == "parallel_property_corresponding_angle":

            version = args[0]

            if version == "1":

                # Expected conclusion (version 1), e.g.:

                # ["Equal(MeasureOfAngle(AEF),MeasureOfAngle(EDH))"]

                m = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conclusions[0])

                if m:

                    angle1, angle2 = m.group(1), m.group(2)

                    a1 = self.add_angle(angle1[0], angle1[1], angle1[2])

                    a2 = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(a1 == a2)

                    print(f"[Version 1] Added parallel corresponding angle equality: {angle1} == {angle2}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Conclusion format error for parallel_property_corresponding_angle (version 1)",

                        details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"

                    )

            elif version == "2":

                # Expected conclusion (version 2), e.g.:

                # ["Equal(MeasureOfAngle(DHF),MeasureOfAngle(BFA))"]

                m = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conclusions[0])

                if m:

                    angle1, angle2 = m.group(1), m.group(2)

                    a1 = self.add_angle(angle1[0], angle1[1], angle1[2])

                    a2 = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(a1 == a2)

                    print(f"[Version 2] Added parallel corresponding angle equality: {angle1} == {angle2}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Conclusion format error for parallel_property_corresponding_angle (version 2)",

                        details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"

                    )





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

            # Expect a conclusion of the form:

            # "Equal(Add(MeasureOfAngle(CAB),MeasureOfAngle(ABC),MeasureOfAngle(BCA)),180)"
            version = args[0]
            if version == "1":
                match = re.search(

                    r'Equal\(Add\(MeasureOfAngle\((\w{3})\),MeasureOfAngle\((\w{3})\),MeasureOfAngle\((\w{3})\)\),180\)',

                    conclusions[0]

                )

                if match:

                    a1, a2, a3 = match.groups()  # e.g., "CAB", "ABC", "BCA"

                    # Add the three angle variables to the solver.

                    angle1_var = self.add_angle(a1[0], a1[1], a1[2])

                    angle2_var = self.add_angle(a2[0], a2[1], a2[2])

                    angle3_var = self.add_angle(a3[0], a3[1], a3[2])

                    # Impose the angle–sum constraint.

                    self.solver.add(angle1_var + angle2_var + angle3_var == 180)

                    print(f"Added triangle angle sum constraint: {a1} + {a2} + {a3} = 180")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Conclusion format error for triangle_property_angle_sum",

                        details=f"Expected pattern Equal(Add(MeasureOfAngle(XXX),MeasureOfAngle(YYY),MeasureOfAngle(ZZZ)),180) but got {conclusions[0]}"

                    )
            elif version == "2":
                print("second")



        elif theorem_name == "similar_triangle_judgment_aa":
            # Expect a conclusion like ["SimilarBetweenTriangle(BAE,CAD)"]
            version = args[0]
            if version == "1":
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

            elif version == "2":
                print("2")


        elif theorem_name == "similar_triangle_property_line_ratio":
            version = args[0]
            if version == "1":
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


                    print(f"Added ratio constraints for all corresponding sides of {tri1} and {tri2}.")
            elif version == "2":
                print("2")



        elif theorem_name == "triangle_perimeter_formula":

            match = re.search(

                r'Equal\(PerimeterOfTriangle\((\w+)\),Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)',

                conclusions[0])

            if match:
                triangle = match.group(1)

                side1 = match.group(2)

                side2 = match.group(3)

                side3 = match.group(4)

                # Create length variables for each side.

                side1_var = self.add_length(side1[0], side1[1])

                side2_var = self.add_length(side2[0], side2[1])

                side3_var = self.add_length(side3[0], side3[1])

                # Calculate the perimeter expression as the sum of side lengths.

                perimeter_expr = side1_var + side2_var + side3_var

                # Create a new Real variable to represent the perimeter of the triangle.

                perimeter_var = Real(f"perimeter_{triangle}")

                # Add the constraint to the solver:

                self.solver.add(perimeter_var == perimeter_expr)

                # Store the variable so that later we can retrieve its value.

                self.triangle_perimeters[triangle] = perimeter_var

                print(
                    f"Added perimeter constraint for triangle {triangle}: {perimeter_var} == {side1_var} + {side2_var} + {side3_var}")


        elif theorem_name == "adjacent_complementary_angle":
            version = args[0]
            if version == "1":
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
            elif version == "2":
                print("2")




        elif theorem_name == "line_addition":

            # Match conclusion pattern: Equal(LengthOfLine(CA),Add(LengthOfLine(CD),LengthOfLine(DA)))

            match = re.search(

                r'Equal\(LengthOfLine\((\w+)\),Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)',

                conclusions[0]

            )

            if not match:
                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message="Invalid conclusion format for line_addition",

                    details="Expected: Equal(LengthOfLine(total),Add(LengthOfLine(part1),LengthOfLine(part2)))"

                )

            total_line, part1, part2 = match.groups()

            # Create or get length variables for all segments

            total_var = self.add_length(total_line[0], total_line[1])

            part1_var = self.add_length(part1[0], part1[1])

            part2_var = self.add_length(part2[0], part2[1])

            # Add the length addition constraint

            self.solver.add(total_var == part1_var + part2_var)

            print(f"Added line addition constraint: {total_line} = {part1} + {part2}")

            return None




        elif theorem_name == "right_triangle_property_pythagorean":
            version = args[0]
            if version == "1":
                # Expecting a conclusion list like:

                # ["Equal(Add(Pow(LengthOfLine(GH),2),Pow(LengthOfLine(HE),2)),Pow(LengthOfLine(GE),2))"]

                match = re.search(

                    r'Equal\(Add\(Pow\(LengthOfLine\((\w+)\),2\),Pow\(LengthOfLine\((\w+)\),2\)\),Pow\(LengthOfLine\((\w+)\),2\)\)',

                    conclusions[0]

                )

                if match:

                    leg1, leg2, hyp = match.group(1), match.group(2), match.group(3)

                    # Retrieve or create the Z3 length variables for the sides.

                    leg1_var = self.add_length(leg1[0], leg1[1])

                    leg2_var = self.add_length(leg2[0], leg2[1])

                    hyp_var = self.add_length(hyp[0], hyp[1])

                    # Ensure the side lengths are positive.

                    self.solver.add(leg1_var > 0, leg2_var > 0, hyp_var > 0)

                    # Add the Pythagorean constraint.

                    self.solver.add(leg1_var * leg1_var + leg2_var * leg2_var == hyp_var * hyp_var)

                    # Optionally, add extra ordering constraints.

                    self.solver.add(leg1_var + leg2_var > hyp_var)

                    self.solver.add(hyp_var > leg1_var, hyp_var > leg2_var)

                    print(f"Added Pythagorean constraint: {leg1}^2 + {leg2}^2 = {hyp}^2")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Conclusion format error for right_triangle_property_pythagorean",

                        details="Expected format: Equal(Add(Pow(LengthOfLine(leg1),2),Pow(LengthOfLine(leg2),2)),Pow(LengthOfLine(hyp),2))"

                    )
            elif version == "2":
                print("2")






        elif theorem_name == "parallel_property_alternate_interior_angle":

            version = args[0]

            if version == "1":

                # Version 1: Use the original behavior.

                m = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conclusions[0])

                if m:

                    angle1, angle2 = m.group(1), m.group(2)

                    a1 = self.add_angle(angle1[0], angle1[1], angle1[2])

                    a2 = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(a1 == a2)

                    print(f"[Version 1] Added constraint: {angle1} == {angle2}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Conclusion format error for parallel_property_alternate_interior_angle (version 1)",

                        details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"

                    )

            elif version == "2":

                # Version 2: For example, expect a different set of angle tokens.

                # In the sample, the conclusion is:

                # "Equal(MeasureOfAngle(GHD),MeasureOfAngle(HGJ))"

                m = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', conclusions[0])

                if m:

                    angle1, angle2 = m.group(1), m.group(2)

                    a1 = self.add_angle(angle1[0], angle1[1], angle1[2])

                    a2 = self.add_angle(angle2[0], angle2[1], angle2[2])

                    self.solver.add(a1 == a2)

                    print(f"[Version 2] Added alternate interior angle constraint: {angle1} == {angle2}")

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Conclusion format error for parallel_property_alternate_interior_angle (version 2)",

                        details="Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY))"

                    )


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

            version = args[0]

            if version == "1":
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
            elif version == "2":
                print("2")

def get_cyclic_variations_rectangle(para_name: str) -> Set[str]:
    """Return all cyclic variations of a polygon name.
    For instance, "PNML" returns {"PNML", "NMLP", "MLPN", "LPNM"}.
    """
    variations = set()
    n = len(para_name)
    for i in range(n):
        variation = para_name[i:] + para_name[:i]
        variations.add(variation)
    return variations


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
        question_match = re.search(r'question[_-]?(\d+)', filename, re.IGNORECASE)
        question_name = f"question_{question_match.group(1)}" if question_match else "unknown_question"
        print(f"Processing {question_name}...")
        with open(filename, 'r') as file:
            content = file.read()

        theorem = GeometricTheorem()
        theorem.question_name = question_name
        result = theorem.parse_and_verify_proof(content)
        print(f"\nOverall verification {'succeeded' if result else 'failed'}")
        return result
    except Exception as e:
        print(f"Error: {str(e)}")
        return False

#/Users/eitan/Desktop/lean/lean_python/questions/the new format for questions after jan_17/new_3_questions/question1/question1_correct
if __name__ == "__main__":
    result = verify_geometric_proof(
        "/Users/eitan/Desktop/lean/lean_python/questions/the new format for questions after jan_17/new_45_questions/question_4254/question4254_oren_to_fix")
    print(f"Verification {'succeeded' if result else 'failed'}")
##