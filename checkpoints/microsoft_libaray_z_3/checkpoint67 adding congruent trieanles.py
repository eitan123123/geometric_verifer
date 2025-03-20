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

        self.triangle_areas = {}
        self.altitude_facts = set()
        self.trapezoids = set()
        self.altitudes = {}
        self.quad_areas = {}
        self.quad_heights = {}

        # For handling both algebraic and numeric expressions
        self.variables = {}
        self.found_tier_1_or_2_error = False
        self.congruent_triangles = []

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
            self.solver.add(self.angles[angle_name] > 0, self.angles[angle_name] <= 180)
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

    def canonicalize_congruent_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Normalize triangles for congruence checking.
        For congruent triangles, we need to consider all possible rotations of both triangles
        and their reflections (since congruence preserves orientation).
        """
        # For first triangle, generate all rotations
        rotations1 = [tri1[i:] + tri1[:i] for i in range(len(tri1))]

        # For second triangle, generate all rotations
        rotations2 = [tri2[i:] + tri2[:i] for i in range(len(tri2))]

        # Also consider all rotations of reversed second triangle (for reflections)
        rev_tri2 = tri2[::-1]
        rotations2_rev = [rev_tri2[i:] + rev_tri2[:i] for i in range(len(rev_tri2))]

        # Combine all possible rotations of the second triangle
        all_rotations2 = rotations2 + rotations2_rev

        # Find the lexicographically smallest pair
        canonical_pair = min((r1, r2) for r1 in rotations1 for r2 in all_rotations2)

        return canonical_pair


    def generate_general_goal_analysis_report(self, goal_expr, expected_value=None):
        """Generate a focused report for general expressions like 'x'"""
        # Create the report content as a string
        report = f"Analysis Report for {self.question_name}\n"
        report += "=" * 60 + "\n\n"
        report += f"Goal expression: {goal_expr}\n"
        if expected_value is not None:
            report += f"Expected value: {expected_value}\n"
        report += "\n"

        # Find all variables directly related to this expression
        related_vars = set()
        if goal_expr in self.variables:
            related_vars.add(goal_expr)

        # Add any variables that relate to this goal expression
        for var_name in self.variables:
            if goal_expr in var_name:  # e.g., 'sin_x' for goal 'x'
                related_vars.add(var_name)

        if related_vars:
            report += "Variables related to this goal:\n"
            report += "-" * 60 + "\n"
            for var in related_vars:
                report += f"- {var}\n"
            report += "\n"
        else:
            report += f"No variables directly related to '{goal_expr}' were found in the system.\n\n"

        # Find all constraints that mention this goal
        relevant_constraints = []
        for c in self.solver.assertions():
            c_str = str(c)
            if goal_expr in c_str:
                relevant_constraints.append(c_str)

        if relevant_constraints:
            report += "Solver constraints directly related to this goal:\n"
            report += "-" * 60 + "\n"
            for i, constraint in enumerate(relevant_constraints):
                report += f"{i + 1}. {constraint}\n"
            report += "\n"
        else:
            report += f"No constraints directly involving '{goal_expr}' were found in the solver.\n\n"

        # Find theorems that relate to this goal
        related_theorems = []
        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if the goal expression is mentioned in the conclusions
            for conclusion in theorem_info["conclusions"]:
                if goal_expr in conclusion:
                    is_related = True
                    break

            # Check if goal is mentioned in the premise
            if goal_expr in theorem_info["premise"]:
                is_related = True

            # Check if goal is mentioned in the args
            if any(goal_expr in arg for arg in theorem_info["args"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "premise": theorem_info["premise"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        if related_theorems:
            report += f"Theorems related to goal {goal_expr}:\n"
            report += "-" * 60 + "\n"
            for theorem in related_theorems:
                report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n"
                report += f"  Premise: {theorem['premise']}\n"
                report += f"  Conclusion: {theorem['conclusion']}\n\n"
        else:
            report += f"No theorems directly involving '{goal_expr}' were found in your proof.\n\n"

        # Check if the solver is unsatisfiable and suggest possible reasons
        report += "Diagnosis:\n"
        report += "-" * 60 + "\n"

        if self.solver.check() == unsat:
            report += "The solver found the constraints to be contradictory. This means your proof contains\n"
            report += "inconsistent constraints that cannot be satisfied simultaneously.\n\n"
        else:
            report += "The solver can find a solution, but there may be other issues preventing verification:\n\n"

        report += "Possible causes:\n"
        report += "1. Incorrect angle or length values in premises\n"
        report += "2. Improper theorem application\n"
        report += "3. Conclusions that contradict earlier assertions\n"
        report += "4. Incorrect algebraic relationships between variables\n\n"

        report += "Try checking your theorem applications, especially those relating directly to\n"
        report += f"the value of {goal_expr}, and verify that your premises are consistent.\n"

        # Return the report content
        return report




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

    def generate_sine_analysis_report(self, angle_token, expected_value, alt_value=None,
                                      solver_state="multiple_values"):
        """Generate a detailed report for sine goals that couldn't be verified."""

        # Create the report content as a string
        report = f"Analysis Report for {self.question_name}\n"
        report += "=" * 60 + "\n\n"
        report += f"Goal: Sine of angle {angle_token}\n"
        report += f"Expected value: {expected_value}\n\n"

        # Extract points involved in the angle
        goal_points = list(angle_token)

        # Find triangles containing this angle
        containing_triangles = []
        for poly in self.polygons:
            if len(poly) == 3 and angle_token[1] in poly:  # Middle letter is the vertex
                containing_triangles.append(poly)

        if containing_triangles:
            report += f"Found {len(containing_triangles)} triangle(s) containing angle {angle_token}:\n"
            for tri in containing_triangles:
                report += f"- Triangle {tri}\n"
                # Check if it's a right triangle
                if tri in self.right_triangles:
                    report += f"  (This is a right triangle)\n"
            report += "\n"

            # For the first triangle, try to analyze the sides
            triangle = containing_triangles[0]
            if self.solver.check() == sat:
                model = self.solver.model()

                # Get vertex indices
                vertex_idx = triangle.index(angle_token[1])
                prev_idx = (vertex_idx - 1) % 3
                next_idx = (vertex_idx + 1) % 3

                # For sine, we need to identify the side opposite to our angle and another side
                opposite_side = self.add_length(triangle[prev_idx], triangle[next_idx])  # Side opposite to vertex
                adjacent1 = self.add_length(triangle[prev_idx], triangle[vertex_idx])  # One adjacent side
                adjacent2 = self.add_length(triangle[vertex_idx], triangle[next_idx])  # Other adjacent side

                try:
                    # Get values
                    opposite_val = float(model.eval(opposite_side).as_decimal(10).rstrip('?'))
                    adjacent1_val = float(model.eval(adjacent1).as_decimal(10).rstrip('?'))
                    adjacent2_val = float(model.eval(adjacent2).as_decimal(10).rstrip('?'))

                    report += f"Side {triangle[prev_idx]}{triangle[next_idx]} (opposite to angle) = {opposite_val}\n"
                    report += f"Side {triangle[prev_idx]}{triangle[vertex_idx]} = {adjacent1_val}\n"
                    report += f"Side {triangle[vertex_idx]}{triangle[next_idx]} = {adjacent2_val}\n\n"

                    # Check if sides are uniquely determined
                    temp_solver = Solver()
                    for c in self.solver.assertions():
                        temp_solver.add(c)

                    # See if we can have different side values
                    epsilon = 1e-8
                    temp_solver.add(Or(
                        Or(opposite_side < opposite_val - epsilon, opposite_side > opposite_val + epsilon),
                        Or(adjacent1 < adjacent1_val - epsilon, adjacent1 > adjacent1_val + epsilon),
                        Or(adjacent2 < adjacent2_val - epsilon, adjacent2 > adjacent2_val + epsilon)
                    ))

                    if temp_solver.check() == unsat:
                        report += "Triangle sides are uniquely determined.\n"

                        # Calculate sine using Law of Sines or right triangle rules
                        if tri in self.right_triangles:
                            # For a right triangle, check if our angle is the right angle
                            right_angle_vertex = None
                            for i in range(3):
                                v = triangle[i]
                                prev = triangle[(i - 1) % 3]
                                next = triangle[(i + 1) % 3]
                                angle_name = f"{prev}{v}{next}"
                                angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])
                                angle_val = float(model.eval(angle_var).as_decimal(10).rstrip('?'))
                                if abs(angle_val - 90) < 0.1:
                                    right_angle_vertex = v
                                    break

                            if right_angle_vertex:
                                report += f"Vertex {right_angle_vertex} has the right angle.\n"

                                # If our angle is the right angle, sin = 1
                                if right_angle_vertex == angle_token[1]:
                                    report += f"Since {angle_token} is the right angle, its sine should be 1.0\n"
                                    if abs(expected_value - 1.0) >= epsilon:
                                        report += f"Error: Expected sine {expected_value} doesn't match 1.0\n"
                                else:
                                    # Otherwise, use sin = opposite/hypotenuse
                                    hypotenuse_vertices = [v for v in triangle if v != right_angle_vertex]
                                    hypotenuse = self.add_length(hypotenuse_vertices[0], hypotenuse_vertices[1])
                                    hypotenuse_val = float(model.eval(hypotenuse).as_decimal(10).rstrip('?'))
                                    report += f"Hypotenuse (opposite to right angle) = {hypotenuse_val}\n"

                                    # For our angle, find opposite side
                                    our_vertex = angle_token[1]
                                    if our_vertex == right_angle_vertex:
                                        # Shouldn't happen as we checked above
                                        pass
                                    else:
                                        other_vertices = [v for v in triangle if v != our_vertex]
                                        opposite_to_our_angle = next(
                                            v for v in other_vertices if v != right_angle_vertex)
                                        side_opposite_to_us = next(
                                            v for v in triangle if v != our_vertex and v != opposite_to_our_angle)

                                        opposite_side_our_angle = self.add_length(opposite_to_our_angle,
                                                                                  side_opposite_to_us)
                                        opposite_val_our_angle = float(
                                            model.eval(opposite_side_our_angle).as_decimal(10).rstrip('?'))

                                        report += f"Side opposite to {angle_token} = {opposite_val_our_angle}\n"

                                        # sin = opposite/hypotenuse
                                        calculated_sin = opposite_val_our_angle / hypotenuse_val
                                        report += f"Calculated sin({angle_token}) = {calculated_sin} (opposite/hypotenuse)\n"

                                        if abs(calculated_sin - expected_value) >= epsilon:
                                            report += f"Error: Calculated sine {calculated_sin} doesn't match expected {expected_value}\n"
                        else:
                            # Not a right triangle - use Law of Sines
                            # First, get the angle value
                            angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])
                            angle_val = float(model.eval(angle_var).as_decimal(10).rstrip('?'))
                            report += f"Angle {angle_token} = {angle_val}°\n"

                            import math
                            calculated_sin = math.sin(math.radians(angle_val))
                            report += f"Calculated sin({angle_token}) = {calculated_sin} from angle measure\n"

                            # Validate using Law of Sines
                            # sin(A)/a = sin(B)/b = sin(C)/c
                            # Get another angle in the triangle
                            other_vertex_idx = (vertex_idx + 1) % 3
                            prev_vertex = triangle[(other_vertex_idx - 1) % 3]
                            next_vertex = triangle[(other_vertex_idx + 1) % 3]
                            other_angle_name = f"{prev_vertex}{triangle[other_vertex_idx]}{next_vertex}"
                            other_angle_var = self.add_angle(other_angle_name[0], other_angle_name[1],
                                                             other_angle_name[2])
                            other_angle_val = float(model.eval(other_angle_var).as_decimal(10).rstrip('?'))

                            other_angle_sin = math.sin(math.radians(other_angle_val))
                            report += f"Other angle {other_angle_name} = {other_angle_val}° with sine = {other_angle_sin}\n"

                            # Get the side opposite to this other angle
                            other_opposite_side = None
                            for i in range(3):
                                if i != other_vertex_idx and i != vertex_idx:
                                    other_opposite_idx = i
                                    break

                            other_opposite_side = self.add_length(triangle[(other_opposite_idx + 1) % 3],
                                                                  triangle[(other_opposite_idx + 2) % 3])
                            other_opposite_val = float(model.eval(other_opposite_side).as_decimal(10).rstrip('?'))

                            # Law of Sines: sin(A)/a = sin(B)/b
                            # Therefore sin(A) = a * sin(B)/b
                            if other_opposite_val > 0 and other_angle_sin > 0:
                                law_of_sines_sin = (opposite_val * other_angle_sin) / other_opposite_val
                                report += f"Using Law of Sines: sin({angle_token}) = {law_of_sines_sin}\n"

                                if abs(law_of_sines_sin - expected_value) >= epsilon:
                                    report += f"Error: Law of Sines gives sine = {law_of_sines_sin}, which doesn't match expected {expected_value}\n"

                            if abs(calculated_sin - expected_value) >= epsilon:
                                report += f"Error: Calculated sine {calculated_sin} doesn't match expected {expected_value}\n"
                    else:
                        report += "Triangle sides are not uniquely determined.\n"
                        report += "This means your proof doesn't establish a specific shape for the triangle.\n"
                except Exception as e:
                    report += f"Error analyzing triangle sides: {str(e)}\n"
        else:
            report += f"No triangles containing angle {angle_token} were found.\n"
            report += "A triangle containing this angle is needed to calculate its sine.\n\n"

        # Look for direct constraints on the angle
        angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])
        if self.solver.check() == sat:
            model = self.solver.model()
            try:
                angle_val = float(model.eval(angle_var).as_decimal(10).rstrip('?'))
                report += f"Current value of angle {angle_token} = {angle_val}°\n"

                # Check if this angle is uniquely determined
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                epsilon = 1e-8
                temp_solver.add(Or(angle_var < angle_val - epsilon, angle_var > angle_val + epsilon))

                if temp_solver.check() == unsat:
                    report += f"Angle {angle_token} is uniquely determined to be {angle_val}°\n"

                    # Calculate expected sine
                    import math
                    expected_sin = math.sin(math.radians(angle_val))
                    report += f"Its sine should be {expected_sin}\n\n"

                    if abs(expected_sin - expected_value) >= epsilon:
                        report += f"Error: Calculated sine {expected_sin} doesn't match expected {expected_value}\n"
                else:
                    alt_model = temp_solver.model()
                    alt_angle = float(alt_model.eval(angle_var).as_decimal(10).rstrip('?'))
                    report += f"Angle {angle_token} is not uniquely determined - could also be {alt_angle}°\n"
                    report += "Your proof needs more constraints to fix this angle to a specific value.\n"
            except Exception as e:
                report += f"Error evaluating angle: {str(e)}\n"

        # Look for direct sine variable
        sine_var_name = f"sin_{angle_token}"
        if sine_var_name in self.variables:
            report += f"\nFound direct sine variable: {sine_var_name}\n"
            sine_var = self.variables[sine_var_name]

            if self.solver.check() == sat:
                model = self.solver.model()
                sine_val = float(model.eval(sine_var).as_decimal(10).rstrip('?'))
                report += f"Current value of sin({angle_token}) = {sine_val}\n"

                # Check if sine is uniquely determined
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                epsilon = 1e-8
                temp_solver.add(Or(sine_var < sine_val - epsilon, sine_var > sine_val + epsilon))

                if temp_solver.check() == unsat:
                    report += f"The value of sin({angle_token}) is uniquely determined to be {sine_val}\n"

                    if abs(sine_val - expected_value) >= epsilon:
                        report += f"Error: Determined sine {sine_val} doesn't match expected {expected_value}\n"
                else:
                    alt_model = temp_solver.model()
                    alt_sine = float(alt_model.eval(sine_var).as_decimal(10).rstrip('?'))
                    report += f"The sine value is not uniquely determined - could also be {alt_sine}\n"

        # Find theorems relevant to this angle
        report += f"\nTheorems related to angle {angle_token} in your proof:\n"
        report += "-" * 60 + "\n"
        related_theorems = []

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if the angle is mentioned in the conclusions
            for conclusion in theorem_info["conclusions"]:
                angle_pattern = f"MeasureOfAngle({angle_token})"
                if angle_pattern in conclusion:
                    is_related = True
                    break

                # Check for normalized variants
                normalized_angle = self.normalize_angle_name(angle_token)
                norm_pattern = f"MeasureOfAngle({normalized_angle})"
                if norm_pattern in conclusion:
                    is_related = True
                    break

                # Also check for Sin(MeasureOfAngle(...))
                sine_pattern = f"Sin(MeasureOfAngle({angle_token}))"
                if sine_pattern in conclusion:
                    is_related = True
                    break

            # Check if mentioned in the premise
            if angle_token in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(angle_token in arg for arg in theorem_info["args"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        if related_theorems:
            for theorem in related_theorems:
                report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n"
                report += f"  Conclusion: {theorem['conclusion']}\n\n"
        else:
            report += f"No theorems directly involving angle {angle_token} were found in your proof.\n\n"

        # Add solver constraints related to this goal
        report += "Solver constraints directly related to this goal:\n"
        report += "-" * 60 + "\n"

        # Normalize the angle name for looking up in solver
        normalized_angle = self.normalize_angle_name(angle_token)
        angle_var_name = f"angle_{normalized_angle}"

        relevant_constraints = []
        for c in self.solver.assertions():
            c_str = str(c)
            if angle_var_name in c_str or sine_var_name in c_str or f"Sin(MeasureOfAngle({angle_token}))" in c_str:
                relevant_constraints.append(c_str)

        if relevant_constraints:
            for i, constraint in enumerate(relevant_constraints):
                report += f"{i + 1}. {constraint}\n"
            report += "\n"
        else:
            report += "No direct constraints found involving this angle's measure or sine.\n\n"

        # Add an explanation based on the solver state
        report += "Diagnosis:\n"
        report += "-" * 60 + "\n"

        if solver_state == "unsatisfiable":
            report += "The solver found the constraints to be contradictory. This means your proof contains\n"
            report += "inconsistent constraints that cannot be satisfied simultaneously.\n\n"
            report += "Possible causes:\n"
            report += "1. Incorrect angle or length values in premises\n"
            report += "2. Improper theorem application\n"
            report += "3. Conclusions that contradict earlier assertions\n"
            report += "4. Errors in the Law of Sines application\n\n"
        elif solver_state == "incompatible":
            report += f"The geometric constraints in your proof don't allow sin({angle_token}) to be {expected_value}.\n"
            report += "This means your proof implies a different sine value than expected.\n\n"
            report += "Check that:\n"
            report += "1. Your triangle side lengths are correctly specified\n"
            report += "2. You've correctly identified the angle in question\n"
            report += "3. There are no errors in your angle constraints\n"
        else:  # multiple_values
            report += f"Your proof doesn't uniquely determine sin({angle_token}).\n"
            report += "Multiple solutions are possible with the current constraints.\n"
            if alt_value is not None:
                report += f"It could be {expected_value} but also {alt_value}\n\n"
            report += "You need to add more constraints by applying additional theorems.\n"
            report += "Focus on fixing the shape of the triangle containing this angle.\n"

        return report

    def generate_division_analysis_report(self, line1, line2, expected_value, alt_value=None,
                                          solver_state="multiple_values"):
        """Generate a detailed report for division goals that couldn't be verified."""

        # Create the report content as a string
        report = f"Analysis Report for {self.question_name}\n"
        report += "=" * 60 + "\n\n"
        report += f"Goal: Division of lines {line1}/{line2}\n"
        report += f"Expected value: {expected_value}\n\n"

        # Extract points involved in the goal lines
        goal_points = list(set(line1 + line2))

        # Check if the lines exist in our geometry
        report += "Analysis of line segments:\n"
        report += "-" * 60 + "\n"

        # Get or create length variables
        len1_var = self.add_length(line1[0], line1[1])
        len2_var = self.add_length(line2[0], line2[1])

        # Check if the solver is satisfiable
        if self.solver.check() == sat:
            model = self.solver.model()

            try:
                # Get current values from the model
                len1_val = float(model.eval(len1_var).as_decimal(10).rstrip('?'))
                len2_val = float(model.eval(len2_var).as_decimal(10).rstrip('?'))

                report += f"Length of {line1}: {len1_val}\n"
                report += f"Length of {line2}: {len2_val}\n"

                # Check for division by zero
                if abs(len2_val) < 1e-10:
                    report += f"Error: Division by zero - line {line2} has length approximately 0\n"
                    report += "This creates a mathematical error when computing the ratio.\n\n"
                else:
                    computed_value = len1_val / len2_val
                    report += f"Computed ratio: {line1}/{line2} = {computed_value}\n\n"

                    epsilon = 1e-8
                    if abs(computed_value - expected_value) >= epsilon:
                        report += f"Error: Computed ratio {computed_value} doesn't match expected {expected_value}\n"
                        report += "This suggests an inconsistency between your proof and the expected answer.\n\n"

                # Check if these lengths are uniquely determined
                report += "Checking uniqueness of line lengths:\n"

                # Check if line1 can have different values
                temp_solver1 = Solver()
                for c in self.solver.assertions():
                    temp_solver1.add(c)

                epsilon = 1e-8
                temp_solver1.add(Or(len1_var < len1_val - epsilon, len1_var > len1_val + epsilon))

                if temp_solver1.check() == sat:
                    alt_model = temp_solver1.model()
                    alt_len1 = float(alt_model.eval(len1_var).as_decimal(10).rstrip('?'))
                    report += f"- Line {line1} is not uniquely determined (could also be {alt_len1})\n"
                else:
                    report += f"- Line {line1} is uniquely determined to be {len1_val}\n"

                # Check if line2 can have different values
                temp_solver2 = Solver()
                for c in self.solver.assertions():
                    temp_solver2.add(c)

                temp_solver2.add(Or(len2_var < len2_val - epsilon, len2_var > len2_val + epsilon))

                if temp_solver2.check() == sat:
                    alt_model = temp_solver2.model()
                    alt_len2 = float(alt_model.eval(len2_var).as_decimal(10).rstrip('?'))
                    report += f"- Line {line2} is not uniquely determined (could also be {alt_len2})\n"
                else:
                    report += f"- Line {line2} is uniquely determined to be {len2_val}\n"

                # Check if the ratio itself can be different while satisfying all constraints
                temp_solver3 = Solver()
                for c in self.solver.assertions():
                    temp_solver3.add(c)

                # We want to check if len1/len2 can have a different value
                # This is equivalent to len1 != expected_value * len2
                temp_solver3.add(Or(
                    len1_var < (expected_value - epsilon) * len2_var,
                    len1_var > (expected_value + epsilon) * len2_var
                ))

                if temp_solver3.check() == sat:
                    alt_model = temp_solver3.model()
                    alt_len1 = float(alt_model.eval(len1_var).as_decimal(10).rstrip('?'))
                    alt_len2 = float(alt_model.eval(len2_var).as_decimal(10).rstrip('?'))

                    # Avoid division by zero
                    if abs(alt_len2) >= 1e-10:
                        alt_ratio = alt_len1 / alt_len2
                        report += f"\nThe ratio {line1}/{line2} is not uniquely determined.\n"
                        report += f"It could be {computed_value} but also {alt_ratio}.\n\n"
                    else:
                        report += f"\nAlternative solution has division by zero issue.\n"
                else:
                    report += f"\nThe ratio {line1}/{line2} is uniquely determined to be {computed_value}.\n\n"

            except Exception as e:
                report += f"Error evaluating line lengths: {str(e)}\n\n"

        # Find geometric relationships that might be relevant
        report += "Geometric relationships involving these line segments:\n"
        report += "-" * 60 + "\n"

        # Check for parallel lines
        # Check for parallel lines
        parallel_relations = set()
        for pair in self.parallel_pairs:
            # Check all combinations and permutations
            pair_options = [
                (line1, line2), (line2, line1),
                (line1[::-1], line2), (line2, line1[::-1]),
                (line1, line2[::-1]), (line2[::-1], line1),
                (line1[::-1], line2[::-1]), (line2[::-1], line1[::-1])
            ]

            if pair in pair_options or (pair[1], pair[0]) in pair_options:
                # Normalize the representation for consistency
                sorted_pair = tuple(sorted([pair[0], pair[1]]))
                parallel_relations.add(f"Lines {sorted_pair[0]} and {sorted_pair[1]} are parallel")

        if parallel_relations:
            for rel in parallel_relations:
                report += f"- {rel}\n"
        else:
            report += "- No parallel relationships found involving these lines\n"

        # Check for perpendicular lines
        perpendicular_relations = []
        for pair in self.perpendicular_pairs:
            # Check all combinations and permutations
            pair_options = [
                (line1, line2), (line2, line1),
                (line1[::-1], line2), (line2, line1[::-1]),
                (line1, line2[::-1]), (line2[::-1], line1),
                (line1[::-1], line2[::-1]), (line2[::-1], line1[::-1])
            ]

            if pair in pair_options or (pair[1], pair[0]) in pair_options:
                perpendicular_relations.append(f"Lines {pair[0]} and {pair[1]} are perpendicular")

        if perpendicular_relations:
            for rel in perpendicular_relations:
                report += f"- {rel}\n"
        else:
            report += "- No perpendicular relationships found involving these lines\n"

        # Check if the lines form a triangle with another line
        triangles_containing_lines = []
        for tri in self.polygons:
            if len(tri) == 3:  # It's a triangle
                if (line1[0] in tri and line1[1] in tri) or (line2[0] in tri and line2[1] in tri):
                    triangles_containing_lines.append(tri)

        if triangles_containing_lines:
            report += "\nTriangles containing these lines:\n"
            for tri in triangles_containing_lines:
                report += f"- Triangle {tri}"
                if tri in self.right_triangles:
                    report += " (right triangle)"
                if hasattr(self, "isosceles_triangles") and tri in self.isosceles_triangles:
                    report += " (isosceles triangle)"
                report += "\n"
        else:
            report += "\nNo triangles found containing these lines\n"

        # Check for similar triangles that might establish the ratio
        if hasattr(self, "similar_triangles"):
            similar_triangles_found = []
            for tri_pair in self.similar_triangles:
                # Check if the lines belong to corresponding sides of similar triangles
                tri1, tri2 = tri_pair
                if (all(p in tri1 for p in line1) and all(p in tri2 for p in line2)) or \
                        (all(p in tri2 for p in line1) and all(p in tri1 for p in line2)):
                    similar_triangles_found.append(tri_pair)

            if similar_triangles_found:
                report += "\nSimilar triangles that may establish this ratio:\n"
                for tri_pair in similar_triangles_found:
                    report += f"- Triangles {tri_pair[0]} and {tri_pair[1]} are similar\n"
                    if tri_pair in self.triangle_ratios:
                        ratio_var = self.triangle_ratios[tri_pair]
                        if self.solver.check() == sat:
                            model = self.solver.model()
                            ratio_val = float(model.eval(ratio_var).as_decimal(10).rstrip('?'))
                            report += f"  (similarity ratio: {ratio_val})\n"
            else:
                report += "\nNo similar triangles found that would establish this ratio\n"

        # Find theorems relevant to these lines
        report += f"\nTheorems related to lines {line1} and {line2} in your proof:\n"
        report += "-" * 60 + "\n"
        related_theorems = []

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if the lines are mentioned in the conclusions
            for conclusion in theorem_info["conclusions"]:
                if f"LengthOfLine({line1})" in conclusion or f"LengthOfLine({line2})" in conclusion:
                    is_related = True
                    break

                # Check for division expressions
                if f"Div(LengthOfLine({line1}),LengthOfLine({line2}))" in conclusion or \
                        f"Div(LengthOfLine({line2}),LengthOfLine({line1}))" in conclusion:
                    is_related = True
                    break

            # Check if mentioned in the premise
            if line1 in theorem_info["premise"] or line2 in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(line1 in arg or line2 in arg for arg in theorem_info["args"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        if related_theorems:
            for theorem in related_theorems:
                report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n"
                report += f"  Conclusion: {theorem['conclusion']}\n\n"
        else:
            report += f"No theorems directly involving lines {line1} or {line2} were found in your proof.\n\n"

        # Add solver constraints related to this goal
        report += "Solver constraints directly related to this goal:\n"
        report += "-" * 60 + "\n"

        len1_var_name = f"length_{self.normalize_line_name(line1)}"
        len2_var_name = f"length_{self.normalize_line_name(line2)}"

        # Use a set to store unique constraints
        relevant_constraints_set = set()
        for c in self.solver.assertions():
            c_str = str(c)
            if (len1_var_name in c_str or len2_var_name in c_str) and not (
                    "1/1000" in c_str or
                    (len1_var_name in c_str and c_str.endswith("> 0")) or
                    (len2_var_name in c_str and c_str.endswith("> 0"))
            ):
                relevant_constraints_set.add(c_str)  # Using a set will eliminate duplicates

        # Convert back to list
        relevant_constraints = list(relevant_constraints_set)

        if relevant_constraints:
            for i, constraint in enumerate(relevant_constraints):
                report += f"{i + 1}. {constraint}\n"
            report += "\n"
        else:
            report += "No direct constraints found involving these lines' lengths.\n\n"

        # Add an explanation based on the solver state
        report += "Diagnosis:\n"
        report += "-" * 60 + "\n"

        if solver_state == "unsatisfiable":
            report += "The solver found the constraints to be contradictory. This means your proof contains\n"
            report += "inconsistent constraints that cannot be satisfied simultaneously.\n\n"
            report += "Possible causes:\n"
            report += "1. Incorrect length values in premises\n"
            report += "2. Improper theorem application\n"
            report += "3. Conclusions that contradict earlier assertions\n"
            report += "4. Errors in the ratio or proportion calculations\n\n"
        elif solver_state == "incompatible":
            report += f"The geometric constraints in your proof don't allow the ratio {line1}/{line2} to be {expected_value}.\n"
            report += "This means your proof implies a different ratio than expected.\n\n"
            report += "Check that:\n"
            report += "1. Your line length values are correctly specified\n"
            report += "2. You've correctly identified the lines in question\n"
            report += "3. Your theorems about proportions or ratios are correctly applied\n"
        else:  # multiple_values
            report += f"Your proof doesn't uniquely determine the ratio {line1}/{line2}.\n"
            report += "Multiple solutions are possible with the current constraints.\n"
            if alt_value is not None:
                report += f"It could be {expected_value} but also {alt_value}\n\n"
            report += "You need to add more constraints by applying additional theorems.\n"
            report += "Consider using theorems about similar triangles, parallel lines,\n"
            report += "or other geometric relationships that fix the proportion between these lines.\n"

        return report

    def generate_cosine_analysis_report(self, angle_token, expected_value, alt_value=None,
                                        solver_state="multiple_values"):
        """Generate a detailed report for cosine goals that couldn't be verified."""

        # Create the report content as a string
        report = f"Analysis Report for {self.question_name}\n"
        report += "=" * 60 + "\n\n"
        report += f"Goal: Cosine of angle {angle_token}\n"
        report += f"Expected value: {expected_value}\n\n"

        # Extract points involved in the angle
        goal_points = list(angle_token)

        # Find triangles containing this angle
        containing_triangles = []
        for poly in self.polygons:
            if len(poly) == 3 and angle_token[1] in poly:  # Middle letter is the vertex
                containing_triangles.append(poly)

        if containing_triangles:
            report += f"Found {len(containing_triangles)} triangle(s) containing angle {angle_token}:\n"
            for tri in containing_triangles:
                report += f"- Triangle {tri}\n"
                # Check if it's a right triangle
                if tri in self.right_triangles:
                    report += f"  (This is a right triangle)\n"
            report += "\n"

            # For the first triangle, try to analyze the sides
            triangle = containing_triangles[0]
            if self.solver.check() == sat:
                model = self.solver.model()

                # Get vertex indices
                vertex_idx = triangle.index(angle_token[1])
                prev_idx = (vertex_idx - 1) % 3
                next_idx = (vertex_idx + 1) % 3

                # Get sides - for cosine, we need the two sides adjacent to our angle
                side1 = self.add_length(triangle[prev_idx], triangle[vertex_idx])  # One adjacent side
                side2 = self.add_length(triangle[vertex_idx], triangle[next_idx])  # Other adjacent side
                opposite = self.add_length(triangle[prev_idx], triangle[next_idx])  # Opposite side

                try:
                    # Get values
                    side1_val = float(model.eval(side1).as_decimal(10).rstrip('?'))
                    side2_val = float(model.eval(side2).as_decimal(10).rstrip('?'))
                    opposite_val = float(model.eval(opposite).as_decimal(10).rstrip('?'))

                    report += f"Side {triangle[prev_idx]}{triangle[vertex_idx]} = {side1_val}\n"
                    report += f"Side {triangle[vertex_idx]}{triangle[next_idx]} = {side2_val}\n"
                    report += f"Side {triangle[prev_idx]}{triangle[next_idx]} = {opposite_val}\n\n"

                    # Check if sides are uniquely determined
                    temp_solver = Solver()
                    for c in self.solver.assertions():
                        temp_solver.add(c)

                    # See if we can have different side values
                    epsilon = 1e-8
                    temp_solver.add(Or(
                        Or(side1 < side1_val - epsilon, side1 > side1_val + epsilon),
                        Or(side2 < side2_val - epsilon, side2 > side2_val + epsilon),
                        Or(opposite < opposite_val - epsilon, opposite > opposite_val + epsilon)
                    ))

                    if temp_solver.check() == unsat:
                        report += "Triangle sides are uniquely determined.\n"

                        # Calculate cosine using Law of Cosines
                        # cos(A) = (b² + c² - a²)/(2bc)
                        # where A is our angle, b & c are adjacent sides, and a is opposite side
                        if side1_val > 0 and side2_val > 0:  # Ensure no division by zero
                            cos_val = (side1_val ** 2 + side2_val ** 2 - opposite_val ** 2) / (
                                        2 * side1_val * side2_val)

                            # Ensure the value is in valid range for cosine
                            cos_val = max(-1, min(1, cos_val))

                            report += f"Calculated cos({angle_token}) = {cos_val} using Law of Cosines\n\n"

                            if abs(cos_val - expected_value) >= epsilon:
                                report += f"Error: Calculated cosine value {cos_val} doesn't match expected {expected_value}\n"
                        else:
                            report += "Error: Zero length side(s) in triangle - cannot calculate cosine\n"
                    else:
                        report += "Triangle sides are not uniquely determined.\n"
                        report += "This means your proof doesn't establish a specific shape for the triangle.\n"

                except Exception as e:
                    report += f"Error analyzing triangle sides: {str(e)}\n"
        else:
            report += f"No triangles containing angle {angle_token} were found.\n"
            report += "A triangle containing this angle is needed to calculate its cosine.\n\n"

        # Look for direct constraints on the angle
        angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])
        if self.solver.check() == sat:
            model = self.solver.model()
            try:
                angle_val = float(model.eval(angle_var).as_decimal(10).rstrip('?'))
                report += f"Current value of angle {angle_token} = {angle_val}°\n"

                # Check if this angle is uniquely determined
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                epsilon = 1e-8
                temp_solver.add(Or(angle_var < angle_val - epsilon, angle_var > angle_val + epsilon))

                if temp_solver.check() == unsat:
                    report += f"Angle {angle_token} is uniquely determined to be {angle_val}°\n"

                    # Calculate expected cosine
                    import math
                    expected_cos = math.cos(math.radians(angle_val))
                    report += f"Its cosine should be {expected_cos}\n\n"

                    if abs(expected_cos - expected_value) >= epsilon:
                        report += f"Error: Calculated cosine {expected_cos} doesn't match expected {expected_value}\n"
                else:
                    alt_model = temp_solver.model()
                    alt_angle = float(alt_model.eval(angle_var).as_decimal(10).rstrip('?'))
                    report += f"Angle {angle_token} is not uniquely determined - could also be {alt_angle}°\n"
                    report += "Your proof needs more constraints to fix this angle to a specific value.\n"
            except Exception as e:
                report += f"Error evaluating angle: {str(e)}\n"

        # Find theorems relevant to this angle
        report += f"\nTheorems related to angle {angle_token} in your proof:\n"
        report += "-" * 60 + "\n"
        related_theorems = []

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if the angle is mentioned in the conclusions
            for conclusion in theorem_info["conclusions"]:
                angle_pattern = f"MeasureOfAngle({angle_token})"
                if angle_pattern in conclusion:
                    is_related = True
                    break

                # Check for normalized variants
                normalized_angle = self.normalize_angle_name(angle_token)
                norm_pattern = f"MeasureOfAngle({normalized_angle})"
                if norm_pattern in conclusion:
                    is_related = True
                    break

            # Check if mentioned in the premise
            if angle_token in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(angle_token in arg for arg in theorem_info["args"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        if related_theorems:
            for theorem in related_theorems:
                report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n"
                report += f"  Conclusion: {theorem['conclusion']}\n\n"
        else:
            report += f"No theorems directly involving angle {angle_token} were found in your proof.\n\n"

        # Add solver constraints related to this goal
        report += "Solver constraints directly related to this goal:\n"
        report += "-" * 60 + "\n"

        # Normalize the angle name for looking up in solver
        normalized_angle = self.normalize_angle_name(angle_token)
        angle_var_name = f"angle_{normalized_angle}"

        # Look for cosine variable
        cos_var_name = f"cos_{angle_token}"

        relevant_constraints = []
        for c in self.solver.assertions():
            c_str = str(c)
            if angle_var_name in c_str or cos_var_name in c_str:
                relevant_constraints.append(c_str)

        if relevant_constraints:
            for i, constraint in enumerate(relevant_constraints):
                report += f"{i + 1}. {constraint}\n"
            report += "\n"
        else:
            report += "No direct constraints found involving this angle's measure or cosine.\n\n"

        # Add an explanation based on the solver state
        report += "Diagnosis:\n"
        report += "-" * 60 + "\n"

        if solver_state == "unsatisfiable":
            report += "The solver found the constraints to be contradictory. This means your proof contains\n"
            report += "inconsistent constraints that cannot be satisfied simultaneously.\n\n"
            report += "Possible causes:\n"
            report += "1. Incorrect angle or length values in premises\n"
            report += "2. Improper theorem application\n"
            report += "3. Conclusions that contradict earlier assertions\n"
            report += "4. Errors in the Law of Cosines application\n\n"
        elif solver_state == "incompatible":
            report += f"The geometric constraints in your proof don't allow cos({angle_token}) to be {expected_value}.\n"
            report += "This means your proof implies a different cosine value than expected.\n\n"
            report += "Check that:\n"
            report += "1. Your triangle side lengths are correctly specified\n"
            report += "2. You've correctly identified the angle in question\n"
            report += "3. There are no errors in your angle constraints\n"
        else:  # multiple_values
            report += f"Your proof doesn't uniquely determine cos({angle_token}).\n"
            report += "Multiple solutions are possible with the current constraints.\n"
            if alt_value is not None:
                report += f"It could be {expected_value} but also {alt_value}\n\n"
            report += "You need to add more constraints by applying additional theorems.\n"
            report += "Focus on fixing the shape of the triangle containing this angle.\n"

        return report





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

        Additionally attempts to compute the ratio value when sufficient constraints exist.
        """
        # Get the canonical pair from our helper.
        canonical_pair = self.canonicalize_mirror_triangle_pair(tri1, tri2)

        # Record the similarity using the canonical pair.
        if canonical_pair not in self.similar_triangles:
            self.similar_triangles.append(canonical_pair)
            print(f"Recorded similarity: triangles {tri1} and {tri2} (canonical: {canonical_pair})")

        # Create a ratio variable if it does not already exist.
        if canonical_pair not in self.triangle_ratios:
            var_name = f"ratio_{canonical_pair[0]}_{canonical_pair[1]}"
            self.triangle_ratios[canonical_pair] = Real(var_name)
            print(f"Created ratio variable: {var_name}")

        ratio_var = self.triangle_ratios[canonical_pair]

        # Try to compute the ratio automatically if solver is satisfiable
        if self.solver.check() == sat:
            model = self.solver.model()

            # Get the vertices of both triangles in their original order
            verts1 = list(tri1)
            verts2 = list(tri2)

            # Check if we can determine the ratio from any pair of corresponding sides
            ratio_determined = False
            attempted_pairs = []

            # Check all three pairs of corresponding sides
            for i in range(3):
                p1a, p1b = verts1[i], verts1[(i + 1) % 3]
                p2a, p2b = verts2[i], verts2[(i + 1) % 3]

                # Form the sides
                side1 = p1a + p1b
                side2 = p2a + p2b

                # Get the length variables
                len1_var = self.add_length(side1[0], side1[1])
                len2_var = self.add_length(side2[0], side2[1])

                attempted_pairs.append((side1, side2))

                # Check if both sides have unique values in the current model
                try:
                    # Create temporary solvers to check uniqueness
                    temp_solver1 = Solver()
                    for c in self.solver.assertions():
                        temp_solver1.add(c)

                    # Get current values
                    len1_val = float(model.eval(len1_var).as_decimal(10).rstrip('?'))
                    len2_val = float(model.eval(len2_var).as_decimal(10).rstrip('?'))

                    # Check uniqueness by trying to find different values
                    epsilon = 1e-8
                    temp_solver1.add(Or(
                        len1_var < len1_val - epsilon,
                        len1_var > len1_val + epsilon
                    ))

                    temp_solver2 = Solver()
                    for c in self.solver.assertions():
                        temp_solver2.add(c)

                    temp_solver2.add(Or(
                        len2_var < len2_val - epsilon,
                        len2_var > len2_val + epsilon
                    ))

                    # If both sides have unique values and second side is non-zero
                    if temp_solver1.check() == unsat and temp_solver2.check() == unsat and len2_val > epsilon:
                        computed_ratio = len1_val / len2_val

                        # Check if this ratio is consistent with existing constraints
                        temp_solver3 = Solver()
                        for c in self.solver.assertions():
                            temp_solver3.add(c)

                        # Try adding the computed ratio
                        temp_solver3.add(ratio_var == computed_ratio)

                        if temp_solver3.check() == sat:
                            # This ratio is consistent, so add it as a constraint
                            self.solver.add(ratio_var == computed_ratio)
                            print(f"✓ Automatically determined similarity ratio: {computed_ratio:.4f}")
                            print(f"  Based on sides: {side1}/{side2} = {len1_val:.4f}/{len2_val:.4f}")
                            ratio_determined = True
                            break
                        else:
                            print(
                                f"× Computed ratio {computed_ratio:.4f} from {side1}/{side2} inconsistent with existing constraints")
                except Exception as e:
                    # Just log and continue - don't disrupt the existing functionality
                    print(f"! Error checking side pair {side1}/{side2}: {str(e)}")

            if not ratio_determined:
                # Also try checking if ratio_var itself is uniquely determined
                try:
                    ratio_val = float(model.eval(ratio_var).as_decimal(10).rstrip('?'))

                    # Check if the ratio is uniquely determined
                    temp_solver = Solver()
                    for c in self.solver.assertions():
                        temp_solver.add(c)

                    epsilon = 1e-8
                    temp_solver.add(Or(
                        ratio_var < ratio_val - epsilon,
                        ratio_var > ratio_val + epsilon
                    ))

                    if temp_solver.check() == unsat:
                        # The ratio is already uniquely determined by existing constraints
                        print(f"✓ Similarity ratio already constrained to: {ratio_val:.4f}")
                        ratio_determined = True
                    else:
                        # To help with debugging, get an alternative value
                        alt_model = temp_solver.model()
                        alt_ratio = float(alt_model.eval(ratio_var).as_decimal(10).rstrip('?'))
                        print(f"! Similarity ratio not uniquely determined: could be {ratio_val} or {alt_ratio}")
                        print(f"  Attempted side pairs: {', '.join([f'{s1}/{s2}' for s1, s2 in attempted_pairs])}")
                except Exception as e:
                    print(f"! Error checking ratio uniqueness: {str(e)}")
        else:
            print("! Note: Cannot compute similarity ratio - solver is unsatisfiable")

        # Add the side ratio constraints for all corresponding sides (for backward compatibility)
        self.add_all_side_ratios_for_similar_triangles(tri1, tri2)

        # Also try to create non-degeneracy constraints for the triangles
        try:
            # Add a constraint that the ratio is positive (prevents zero-sized solutions)
            self.solver.add(ratio_var > 0)

            # Add constraints that all sides have positive length
            for tri in [tri1, tri2]:
                for i in range(3):
                    p1 = tri[i]
                    p2 = tri[(i + 1) % 3]
                    side_var = self.add_length(p1, p2)
                    # Use a small positive value instead of 0 to prevent near-zero solutions
                    self.solver.add(side_var > 0.001)
        except Exception as e:
            # Just log, don't disrupt existing functionality
            print(f"! Error adding non-degeneracy constraints: {str(e)}")

        return ratio_var  # Return the ratio variable for convenience


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

    def generate_length_analysis_report(self, line_name, expected_value, alt_value=None,
                                        solver_state="multiple_values"):
        """Generate a focused report about why the line length goal couldn't be uniquely determined"""

        # Create the report content as a string
        report = f"Analysis Report for {self.question_name}\n"
        report += "=" * 60 + "\n\n"
        report += f"Goal: Length of line {line_name}\n"
        report += f"Expected value: {expected_value}\n\n"

        # Extract points involved in the line
        line_points = list(line_name)

        # Get all related facts from our knowledge base
        related_facts = self.collect_related_facts_for_line(line_points)

        if related_facts:
            report += "Relevant geometric facts:\n"
            report += "-" * 60 + "\n"
            for category, facts in related_facts.items():
                if facts:  # Only show categories with facts
                    report += f"{category}:\n"
                    for fact in facts:
                        report += f"  - {fact}\n"
                    report += "\n"
        else:
            report += "No facts directly involving line " + line_name + " were found in the premises.\n\n"

        # Find theorems that mention the line or its components
        report += f"Theorems related to line {line_name} in your proof:\n"
        report += "-" * 60 + "\n"

        related_theorems = self.find_related_theorems_for_line(line_name, line_points)

        if related_theorems:
            for theorem in related_theorems:
                report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n"
                report += f"  Conclusion: {theorem['conclusion']}\n\n"
        else:
            report += f"No theorems directly involving line {line_name} were found in your proof.\n\n"

        # Add solver constraints related to this line
        report += "Solver constraints directly related to this line:\n"
        report += "-" * 60 + "\n"

        # Normalize the line name for looking up in solver
        normalized_line = self.normalize_line_name(line_name)
        length_var_name = f"length_{normalized_line}"

        # More precise constraint filtering
        relevant_constraints = []
        for c in self.solver.assertions():
            c_str = str(c)
            # Only include constraints that directly mention the exact line variable name
            if length_var_name in c_str:
                # Check for direct relationships with this line
                patterns = [
                    f"{length_var_name} " in c_str,
                    f"{length_var_name}=" in c_str,
                    f"{length_var_name}+" in c_str,
                    f"{length_var_name}-" in c_str,
                    f"{length_var_name}*" in c_str,
                    f"{length_var_name}/" in c_str
                ]
                if any(patterns):
                    relevant_constraints.append(c_str)

            # Also include constraints that set the line value
            elif f" == {length_var_name}" in c_str:
                relevant_constraints.append(c_str)

        if relevant_constraints:
            for i, constraint in enumerate(relevant_constraints):
                report += f"{i + 1}. {constraint}\n"
            report += "\n"
        else:
            report += "No direct constraints found involving this line length.\n\n"

        # Add different explanations based on solver state
        report += "Diagnosis:\n"
        report += "-" * 60 + "\n"

        if solver_state == "unsatisfiable":
            report += f"The solver found the constraints to be contradictory when trying to evaluate length of {line_name}.\n"
            report += "This means there's an inconsistency in your geometric setup or theorem applications.\n"
            report += "Check for contradictory premises or incorrectly applied theorems.\n"
        elif solver_state == "incompatible":
            report += f"The constraints in your proof are consistent, but don't allow line {line_name} to be {expected_value}.\n"
            report += "This means your proof implies a different value for this line than expected.\n"
        elif solver_state == "undefined":
            report += f"The line {line_name} is not defined in your proof's context.\n"
            report += "This usually means you haven't created constraints for this line in your theorems.\n"
            report += "Check that you've properly established this line using appropriate theorems.\n"
        else:  # multiple_values
            report += f"Your proof doesn't uniquely determine the length of line {line_name}.\n"
            report += "Multiple solutions are possible with the current constraints.\n"
            if alt_value is not None:
                report += f"It could be {expected_value} but also {alt_value}\n"
            report += "You need to add more constraints by applying additional theorems.\n"

        return report

    def collect_related_facts_for_line(self, line_points):
        """Collect only facts where at least one point is part of the line"""
        related_facts = {}
        line_points_set = set(line_points)

        # 1. Points in the line
        related_facts["Points"] = line_points

        # 2. Collect lines containing at least one point from our line
        related_lines = []
        for line_name, line_var in self.lengths.items():
            # Extract points from line name (typically in format "length_AB")
            line_points_str = line_name.split('_')[1] if '_' in line_name else line_name
            if any(p in line_points_set for p in line_points_str) and line_points_str != ''.join(line_points):
                related_lines.append(f"Line {line_points_str}")
        related_facts["Related Lines"] = related_lines

        # 3. Collect triangles containing both points of our line
        related_triangles = []
        for polygon in self.polygons:
            if len(polygon) == 3 and all(p in polygon for p in line_points):
                properties = []
                if polygon in self.right_triangles:
                    properties.append("right")
                if hasattr(self, 'isosceles_triangles') and polygon in self.isosceles_triangles:
                    properties.append("isosceles")
                if properties:
                    related_triangles.append(f"Triangle {polygon} ({', '.join(properties)})")
                else:
                    related_triangles.append(f"Triangle {polygon}")
        related_facts["Triangles Containing This Line"] = related_triangles

        # 4. Collect quadrilaterals containing both points of our line
        related_quads = []
        for polygon in self.polygons:
            if len(polygon) == 4 and all(p in polygon for p in line_points):
                properties = []
                if polygon in self.parallelograms:
                    properties.append("parallelogram")
                if hasattr(self, 'rectangles') and polygon in self.rectangles:
                    properties.append("rectangle")
                if hasattr(self, 'squares') and polygon in self.squares:
                    properties.append("square")
                if properties:
                    related_quads.append(f"Quadrilateral {polygon} ({', '.join(properties)})")
                else:
                    related_quads.append(f"Quadrilateral {polygon}")
        related_facts["Quadrilaterals Containing This Line"] = related_quads

        # 5. Collect parallel line pairs involving this line
        related_parallel = []
        line_str = ''.join(line_points)
        for pair in self.parallel_pairs:
            if line_str in [pair[0], pair[1], pair[0][::-1], pair[1][::-1]]:
                other_line = pair[1] if (pair[0] == line_str or pair[0][::-1] == line_str) else pair[0]
                related_parallel.append(f"Parallel to {other_line}")
        related_facts["Parallel Relationships"] = related_parallel

        # 6. Collect perpendicular line pairs involving this line
        related_perp = []
        for pair in self.perpendicular_pairs:
            if line_str in [pair[0], pair[1], pair[0][::-1], pair[1][::-1]]:
                other_line = pair[1] if (pair[0] == line_str or pair[0][::-1] == line_str) else pair[0]
                related_perp.append(f"Perpendicular to {other_line}")
        related_facts["Perpendicular Relationships"] = related_perp

        # 7. Check if this line is a radius, diameter, or chord of a circle
        circle_relationships = []
        for circle, center in self.circle_centers.items():
            if center in line_points and any(p != center and p in line_points for p in line_points):
                circle_relationships.append(f"Radius of circle {circle}")

        for diam_tuple in self.is_diameter_of_circle:
            diam_line, circle = diam_tuple
            if diam_line == line_str or diam_line[::-1] == line_str:
                circle_relationships.append(f"Diameter of circle {circle}")

        related_facts["Circle Relationships"] = circle_relationships

        # Remove empty categories
        return {k: v for k, v in related_facts.items() if v}

    def find_related_theorems_for_line(self, line_name, line_points):
        """Find theorems that directly relate to the line"""
        related_theorems = []
        line_points_set = set(line_points)

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if line is directly mentioned in conclusions
            for conclusion in theorem_info["conclusions"]:
                if f"LengthOfLine({line_name})" in conclusion:
                    is_related = True
                    break

                # Look for normalized versions
                norm_line = self.normalize_line_name(line_name)
                if f"LengthOfLine({norm_line})" in conclusion:
                    is_related = True
                    break

            # Check if mentioned in the premise
            if line_name in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(line_name in arg for arg in theorem_info["args"]):
                is_related = True

            # Check if any of the points is mentioned in a side ratio or similar triangle context
            if any("RatioOfSimilarTriangle" in c and any(p in c for p in line_points) for c in
                   theorem_info["conclusions"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        return related_theorems




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

    def write_failure_report(self, goal_token, report_content):
        """Write a failure report to a file with timestamp"""
        import os
        import datetime

        # Create the directory if it doesn't exist
        output_dir = "info"
        os.makedirs(output_dir, exist_ok=True)

        # Create a timestamped filename - use ONLY the question name, not the goal token
        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"{output_dir}/{self.question_name}_{timestamp}.txt"

        # Write the analysis file
        with open(filename, 'w') as f:
            f.write(report_content)

        print(f"\nDetailed analysis written to: {filename}")
        return filename

    # Modified verify_goal_arc function with enhanced feedback
    def verify_goal_arc(self, arc_name: str, expected: float, epsilon: float = 1e-8) -> tuple:
        goal_arc = arc_name
        print(f"\nVerifying arc goal: {goal_arc}")

        # Create a report
        arc_report = f"Analysis Report for {self.question_name}\n"
        arc_report += "=" * 60 + "\n\n"
        arc_report += f"Goal: MeasureOfArc({goal_arc})\n"
        arc_report += f"Expected value: {expected}\n\n"

        arc_var = self.arcs.get(f"arc_{self.normalize_arc(arc_name)}")
        if arc_var is None:
            error_msg = "Arc variable not defined."
            arc_report += "Error: Arc variable not defined.\n"
            print("Arc variable not defined.")

            # Generate a detailed report for this case
            goal_points = list(arc_name)
            detailed_report = self.generate_goal_analysis_report(arc_name, expected, None, "undefined")
            arc_report += f"\n{detailed_report}\n"

            # Write report to file
            self.write_failure_report(f"arc_{goal_arc}", arc_report)
            return False, arc_report

        if self.solver.check() == sat:
            # First check if constraints allow the expected value
            temp_solver1 = Solver()
            for c in self.solver.assertions():
                temp_solver1.add(c)

            # Add constraint that arc_var == expected (within epsilon)
            temp_solver1.add(And(arc_var >= expected - epsilon, arc_var <= expected + epsilon))

            if temp_solver1.check() != sat:
                error_msg = f"Failed to prove arc measure goal: constraints don't allow the expected value."
                arc_report += f"Error: Constraints don't allow the expected arc measure {expected}\n"

                # Generate a detailed report for this case
                detailed_report = self.generate_goal_analysis_report(arc_name, expected, None, "incompatible")
                arc_report += f"\n{detailed_report}\n"

                print(f"Error: Constraints don't allow the expected arc measure {expected}")
                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message=error_msg,
                    details=f"Goal was: MeasureOfArc({arc_name}) = {expected}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")

                # Write report to file
                self.write_failure_report(f"arc_{goal_arc}", arc_report)
                return False, arc_report

            # Now check if any other value is allowed
            temp_solver2 = Solver()
            for c in self.solver.assertions():
                temp_solver2.add(c)

            # Add constraint: arc_var != expected (outside epsilon range)
            temp_solver2.add(Or(arc_var < expected - epsilon, arc_var > expected + epsilon))

            if temp_solver2.check() == sat:
                alt_model = temp_solver2.model()
                alt_value = float(alt_model.eval(arc_var).as_decimal(10).rstrip('?'))

                error_msg = f"Failed to prove arc measure goal: constraints allow multiple values."
                arc_report += f"Error: The proof doesn't uniquely determine arc measure {goal_arc}.\n"
                arc_report += f"It could be {expected} but also {alt_value}\n"

                # Generate a detailed report for this case
                detailed_report = self.generate_goal_analysis_report(arc_name, expected, alt_value, "multiple_values")
                arc_report += f"\n{detailed_report}\n"

                print(f"Error: The proof doesn't uniquely determine arc measure {goal_arc}.")
                print(f"It could be {expected} but also {alt_value}")

                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message=error_msg,
                    details=f"Goal was: MeasureOfArc({arc_name}) = {expected}, but could also be {alt_value}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")

                # Write report to file
                self.write_failure_report(f"arc_{goal_arc}", arc_report)
                return False, arc_report

            # If we get here, the constraints uniquely determine the value to be expected
            model = self.solver.model()
            calc_expr = model.eval(arc_var)
            val_str = calc_expr.as_decimal(10)
            if val_str.endswith('?'):
                val_str = val_str[:-1]
            calculated_value = float(val_str)
            print(f"Calculated value for MeasureOfArc({arc_name}) is {calculated_value}")
            print(f"Success: Arc measure {goal_arc} is uniquely determined to be {expected}.")
            return True, ""
        else:
            error_msg = "Failed to prove arc measure goal: solver is unsatisfiable."
            arc_report += "Error: Solver constraints unsatisfiable when verifying arc goal.\n"

            # Generate a detailed report for unsatisfiable case
            detailed_report = self.generate_goal_analysis_report(arc_name, expected, None, "unsatisfiable")
            arc_report += f"\n{detailed_report}\n"

            print("Solver constraints unsatisfiable when verifying arc goal.")
            error = GeometricError(
                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                message=error_msg,
                details=f"Goal: MeasureOfArc({arc_name}) = {expected}"
            )
            print(f"\nError in {error.tier.name}: {error.message}")

            # Write report to file
            self.write_failure_report(f"arc_{goal_arc}", arc_report)
            return False, arc_report

    def verify_goal_length(self, p1: str, p2: str, expected: float, epsilon: float = 1e-8) -> tuple:
        goal_line = p1 + p2
        normalized = self.normalize_line_name(goal_line)
        print(f"\nVerifying length goal: {normalized}")
        print(f"Expected value: {expected}")

        # Create a report
        length_report = f"Analysis Report for {self.question_name}\n"
        length_report += "=" * 60 + "\n\n"
        length_report += f"Goal: LengthOfLine({normalized})\n"
        length_report += f"Expected value: {expected}\n\n"

        # Get the length variable.
        length_var = self.lengths.get(f"length_{normalized}")
        if length_var is None:
            error_msg = "Length variable not defined."
            length_report += "Error: Length variable not defined.\n"
            print("Length variable not defined.")

            # Generate a detailed report using the new line-specific function
            detailed_report = self.generate_length_analysis_report(goal_line, expected, None, "undefined")
            length_report += f"\n{detailed_report}\n"

            # Write report to file
            self.write_failure_report(f"length_{normalized}", length_report)
            return False, length_report

        if self.solver.check() == sat:
            # Check if the length is forced to be exactly expected
            temp_solver1 = Solver()
            for c in self.solver.assertions():
                temp_solver1.add(c)

            # Add constraint that length_var == expected (within epsilon)
            temp_solver1.add(And(length_var >= expected - epsilon, length_var <= expected + epsilon))

            # If this is unsat, the constraints don't allow the expected value
            if temp_solver1.check() != sat:
                error_msg = f"Failed to prove length goal: constraints don't allow the expected value."
                length_report += f"Error: Constraints don't allow the expected value {expected}\n"

                # Generate a detailed report using the new line-specific function
                detailed_report = self.generate_length_analysis_report(goal_line, expected, None, "incompatible")
                length_report += f"\n{detailed_report}\n"

                print(f"Error: Constraints don't allow the expected value {expected}")
                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message=error_msg,
                    details=f"Goal was: LengthOfLine({normalized}) = {expected}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")

                # Write report to file
                self.write_failure_report(f"length_{normalized}", length_report)
                return False, length_report

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

                error_msg = f"Failed to prove length goal: constraints allow multiple values."
                length_report += f"Error: The proof doesn't uniquely determine {normalized}.\n"
                length_report += f"It could be {expected} but also {alt_value}\n"

                # Generate a detailed report using the new line-specific function
                detailed_report = self.generate_length_analysis_report(goal_line, expected, alt_value,
                                                                       "multiple_values")
                length_report += f"\n{detailed_report}\n"

                print(f"Error: The proof doesn't uniquely determine {normalized}.")
                print(f"It could be {expected} but also {alt_value}")

                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message=error_msg,
                    details=f"Goal was: LengthOfLine({normalized}) = {expected}, but could also be {alt_value}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")

                # Write report to file
                self.write_failure_report(f"length_{normalized}", length_report)
                return False, length_report

            # If we get here, the constraints uniquely determine the value
            print(f"Success: The length {normalized} is uniquely determined to be {expected}.")
            return True, ""
        else:
            error_msg = f"Failed to prove length goal: solver is unsatisfiable."
            length_report += "Error: Solver constraints unsatisfiable when verifying length goal.\n"

            # Generate a detailed report using the new line-specific function
            detailed_report = self.generate_length_analysis_report(goal_line, expected, None, "unsatisfiable")
            length_report += f"\n{detailed_report}\n"

            print("Solver constraints unsatisfiable when verifying length goal.")
            error = GeometricError(
                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                message=error_msg,
                details=f"Goal: LengthOfLine({normalized}) = {expected}"
            )
            print(f"\nError in {error.tier.name}: {error.message}")

            # Write report to file
            self.write_failure_report(f"length_{normalized}", length_report)
            return False, length_report

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

    # Add this helper function to your GeometricTheorem class
    def evaluate_general_sub_expression(self, goal_expr, model):
        """Parse and evaluate a Sub() expression, including angle measures"""
        # Extract the two operands from Sub(expr1, expr2)
        inner = goal_expr[4:-1]  # Remove Sub( and )
        parts = inner.split(',')
        if len(parts) != 2:
            raise ValueError(f"Sub expression expected 2 parts, got: {len(parts)}")

        expr1_str = parts[0].strip()
        expr2_str = parts[1].strip()

        # Check for angle measure patterns
        angle1_match = re.match(r'MeasureOfAngle\((\w+)\)', expr1_str)
        angle2_match = re.match(r'MeasureOfAngle\((\w+)\)', expr2_str)

        if angle1_match and angle2_match:
            angle1_name = angle1_match.group(1)
            angle2_name = angle2_match.group(1)

            # Get angle variables
            angle1_var = self.add_angle(angle1_name[0], angle1_name[1], angle1_name[2])
            angle2_var = self.add_angle(angle2_name[0], angle2_name[1], angle2_name[2])

            # Evaluate each angle
            angle1_val = float(model.eval(angle1_var).as_decimal(10).rstrip('?'))
            angle2_val = float(model.eval(angle2_var).as_decimal(10).rstrip('?'))

            # Return the difference
            return angle1_val - angle2_val

        # Add other Sub() patterns as needed here
        # For example, you can add support for other types of measures

        # If no pattern matches, raise an error
        raise ValueError(f"Unsupported Sub expression format: {goal_expr}")




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
        elif theorem_name == "congruent_triangle_property_angle_equal":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Insufficient arguments for congruent_triangle_property_angle_equal",
                        details="Expected: congruent_triangle_property_angle_equal(1, triangle1, triangle2)"
                    ))

                tri1, tri2 = args[1].strip(), args[2].strip()

                # Check for congruence in premise
                congruent_match = re.search(r'CongruentBetweenTriangle\((\w+),(\w+)\)', premise)
                if not congruent_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing CongruentBetweenTriangle(...) in premise",
                        details="congruent_triangle_property_angle_equal requires congruent triangles"
                    ))

                premise_tri1, premise_tri2 = congruent_match.groups()

                # Create canonical representations for theorem triangles and premise triangles
                theorem_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)
                premise_pair = self.canonicalize_congruent_triangle_pair(premise_tri1, premise_tri2)

                # Check if triangles in premise match those in theorem call using canonical form
                if theorem_pair != premise_pair:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Triangles in premise ({premise_tri1}, {premise_tri2}) don't match those in theorem call ({tri1}, {tri2})",
                        details="Triangles must match between premise and theorem call"
                    ))

                # Check if these triangles are recorded as congruent using canonical form
                canonical_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)
                if canonical_pair not in self.congruent_triangles:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Triangles {tri1} and {tri2} not proven congruent",
                        details="Required for congruent_triangle_property_angle_equal"
                    ))

                return True, None

        elif theorem_name == "congruent_triangle_property_line_equal":

            version = args[0]

            if version == "1":

                if len(args) < 3:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Insufficient arguments for congruent_triangle_property_line_equal",

                        details="Expected: congruent_triangle_property_line_equal(1, triangle1, triangle2)"

                    ))

                tri1, tri2 = args[1].strip(), args[2].strip()

                # Check for congruence in premise

                congruent_match = re.search(r'CongruentBetweenTriangle\((\w+),(\w+)\)', premise)

                if not congruent_match:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message="Missing CongruentBetweenTriangle(...) in premise",

                        details="congruent_triangle_property_line_equal requires congruent triangles"

                    ))

                premise_tri1, premise_tri2 = congruent_match.groups()

                # Create canonical representations for theorem triangles and premise triangles

                theorem_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)

                premise_pair = self.canonicalize_congruent_triangle_pair(premise_tri1, premise_tri2)

                # Check if triangles in premise match those in theorem call using canonical form

                if theorem_pair != premise_pair:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"Triangles in premise ({premise_tri1}, {premise_tri2}) don't match those in theorem call ({tri1}, {tri2})",

                        details="Triangles must match between premise and theorem call"

                    ))

                # Check if these triangles are recorded as congruent using canonical form

                canonical_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)

                if canonical_pair not in self.congruent_triangles:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"Triangles {tri1} and {tri2} not proven congruent",

                        details="Required for congruent_triangle_property_line_equal"

                    ))

                return True, None


        elif theorem_name == "median_of_triangle_judgment":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing arguments for median_of_triangle_judgment",
                        details="Expected median_of_triangle_judgment(1, median_line, triangle)"
                    ))

                median_line = args[1].strip()  # e.g., "EM"
                triangle = args[2].strip()  # e.g., "EBC"

                # Check if the triangle exists in our polygon database
                # if self.normalize_triangle(triangle) not in self.polygons:
                #     return return_error(GeometricError(
                #         tier=ErrorTier.TIER2_PREMISE,
                #         message=f"Triangle {triangle} is not defined in the geometric data",
                #         details=f"Known polygons: {self.polygons}"
                #     ))

                # Check if the line exists
                # line_match = re.search(r'Line\((\w+)\)', premise)
                # if not line_match or line_match.group(1) != median_line:
                #     return return_error(GeometricError(
                #         tier=ErrorTier.TIER2_PREMISE,
                #         message=f"Line {median_line} is not defined in the premise",
                #         details="A median must be a defined line"
                #     ))

                # Extract the opposite side vertices (not connected to median's vertex)
                # For a median from E to M in triangle EBC, we need to check if M is on BC
                endpoints = median_line[0] + median_line[1]  # "EM"
                median_vertex = median_line[0]  # "E"
                median_foot = median_line[1]  # "M"

                # The other two vertices should be the remaining ones in the triangle
                other_vertices = [v for v in triangle if v != median_vertex]  # ["B", "C"]

                # Check if the collinearity fact exists for the median foot and the opposite side
                collinear_match = re.search(r'Collinear\((\w+)\)', premise)
                if not collinear_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing collinearity in premise",
                        details="A median requires collinearity of the foot and the opposite side"
                    ))

                collinear_points = collinear_match.group(1)  # "BMC"

                # Check that the median foot and the other vertices are collinear
                if not (median_foot in collinear_points and all(v in collinear_points for v in other_vertices)):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Incorrect collinearity for median judgment",
                        details=f"Need collinearity between median foot {median_foot} and opposite vertices {other_vertices}"
                    ))

                # Check for the length equality fact
                length_eq_match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', premise)
                if not length_eq_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing length equality in premise",
                        details="A median requires equal lengths on both sides of the foot"
                    ))

                side1, side2 = length_eq_match.groups()  # "BM", "CM"

                # Ensure this equality is for the segments formed by the median foot
                expected_segments = [median_foot + other_vertices[0], other_vertices[0] + median_foot,
                                     median_foot + other_vertices[1], other_vertices[1] + median_foot]

                if not ((side1 in expected_segments) and (side2 in expected_segments)):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Incorrect length equality for median judgment",
                        details=f"The lengths must be for segments connecting the median foot to the opposite vertices"
                    ))

                return True, None


        # In the validate_theorem_premises method
        elif theorem_name == "right_triangle_property_length_of_median":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing arguments for right_triangle_property_length_of_median",
                        details="Expected right_triangle_property_length_of_median(1, triangle, median_endpoint)"
                    ))

                triangle = args[1].strip()  # e.g., "CEB"
                median_endpoint = args[2].strip()  # e.g., "M"

                # Check if the triangle is a right triangle
                if self.normalize_triangle(triangle) not in self.right_triangles:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Triangle {triangle} is not proven to be a right triangle",
                        details=f"Known right triangles: {self.right_triangles}"
                    ))

                # Check if the median has been established
                # We need to reconstruct the median line and find its start point
                # Since we only have the endpoint M, we need to find the starting vertex

                # Find the IsMedianOfTriangle fact in self.medians
                median_found = False
                median_line = ""
                median_triangle = ""

                for median, tri in self.medians:
                    if median_endpoint in median and self.normalize_triangle(tri) == self.normalize_triangle(triangle):
                        median_found = True
                        median_line = median
                        median_triangle = tri
                        break

                if not median_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Median ending at {median_endpoint} for triangle {triangle} not established",
                        details="Need to first establish the median using median_of_triangle_judgment"
                    ))

                # Ensure that the median is to the hypotenuse of the right triangle
                # In a right triangle, the hypotenuse is opposite to the right angle

                # Find which vertex has the right angle
                right_angle_vertex = None
                for i in range(3):
                    v1 = triangle[i]
                    v2 = triangle[(i + 1) % 3]
                    v3 = triangle[(i + 2) % 3]
                    angle = self.normalize_angle_name(v1 + v2 + v3)
                    angle_var = self.angles.get(f"angle_{angle}")

                    if angle_var is not None:
                        # Check if this angle is constrained to be 90 degrees
                        temp_solver = Solver()
                        for c in self.solver.assertions():
                            temp_solver.add(c)
                        temp_solver.add(angle_var != 90)
                        if temp_solver.check() == unsat:
                            right_angle_vertex = v2
                            break

                if right_angle_vertex is None:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Could not determine the right angle in triangle {triangle}",
                        details="A right triangle must have one angle of 90 degrees"
                    ))

                # The two vertices that are not the right angle vertex form the hypotenuse
                hypotenuse_vertices = [v for v in triangle if v != right_angle_vertex]

                # Check that the median is from the right angle to the midpoint of the hypotenuse
                median_start = median_line[0]

                if median_start != right_angle_vertex:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Median {median_line} is not from the right angle to the hypotenuse",
                        details=f"The median must start at the right angle vertex {right_angle_vertex}"
                    ))

                return True, None


        # In the validate_theorem_premises method
        elif theorem_name == "median_of_triangle_judgment":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing arguments for median_of_triangle_judgment",
                        details="Expected median_of_triangle_judgment(1, median_line, triangle)"
                    ))

                median_line = args[1].strip()  # e.g., "EM"
                triangle = args[2].strip()  # e.g., "EBC"

                # Check if the triangle exists in our polygon database
                if self.normalize_triangle(triangle) not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Triangle {triangle} is not defined in the geometric data",
                        details=f"Known polygons: {self.polygons}"
                    ))

                # Extract the median vertex and foot
                median_vertex = median_line[0]  # "E"
                median_foot = median_line[1]  # "M"

                # The other two vertices should be the remaining ones in the triangle
                other_vertices = [v for v in triangle if v != median_vertex]  # ["B", "C"]

                # Check if there is a collinearity fact containing the median foot and the opposite vertices
                collinear_found = False
                for fact in self.collinear_facts:
                    fact_str = ''.join(fact)
                    if median_foot in fact_str and all(v in fact_str for v in other_vertices):
                        collinear_found = True
                        break

                if not collinear_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing collinearity for median judgment",
                        details=f"Need collinearity between median foot {median_foot} and opposite vertices {other_vertices}"
                    ))

                # Check if the lengths of the segments are equal
                segment1 = median_foot + other_vertices[0]  # "MB"
                segment2 = median_foot + other_vertices[1]  # "MC"

                normalized_segment1 = self.normalize_line_name(segment1)
                normalized_segment2 = self.normalize_line_name(segment2)

                # Check if the lengths are forced to be equal by the solver
                length1_var = self.add_length(normalized_segment1[0], normalized_segment1[1])
                length2_var = self.add_length(normalized_segment2[0], normalized_segment2[1])

                # Create a temporary solver with all current constraints
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                # If adding the inequality makes the system unsat, then they are equal
                temp_solver.add(length1_var != length2_var)
                if temp_solver.check() != unsat:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Equal segment lengths not established for median",
                        details=f"Segments {normalized_segment1} and {normalized_segment2} must be equal"
                    ))

                return True, None



        elif theorem_name == "incenter_of_triangle_judgment_intersection":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing arguments for incenter_of_triangle_judgment_intersection",
                        details="Expected incenter_of_triangle_judgment_intersection(1, point, triangle)"
                    ))

                point = args[1].strip()  # e.g., "O"
                triangle = args[2].strip()  # e.g., "ABC"

                # Check that polygon exists
                polygon_match = re.search(r'Polygon\((\w+)\)', premise)
                if not polygon_match or polygon_match.group(1) != triangle:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Missing or incorrect polygon in premise",
                        details=f"Expected Polygon({triangle})"
                    ))

                # Check for angle bisector facts
                bisector_pattern = r'IsBisectorOfAngle\((\w+),(\w+)\)'
                bisector_matches = re.findall(bisector_pattern, premise)

                if len(bisector_matches) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing angle bisector facts",
                        details="Need at least two angle bisectors to determine incenter"
                    ))

                # Verify each angle bisector
                for line, angle in bisector_matches:
                    # Check if the line contains the point O
                    if point not in line:
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Angle bisector {line} does not contain point {point}",
                            details="Angle bisector must contain the incenter"
                        ))

                return True, None

        elif theorem_name == "vertical_angle":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Insufficient arguments for vertical_angle",
                        details="Expected vertical_angle(1, angle1, angle2)"
                    ))

                angle1 = args[1].strip()  # e.g., "DEB"
                angle2 = args[2].strip()  # e.g., "CEA"

                # Parse the premise parts
                premise_parts = premise.split('&')

                # Check for at least 4 parts (2 collinear facts and 2 angle facts)
                if len(premise_parts) < 4:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Incomplete premise for vertical_angle",
                        details="Expected 2 collinear facts and 2 angle facts"
                    ))

                # Extract and verify collinear facts
                collinear_parts = [p for p in premise_parts if p.startswith("Collinear")]
                if len(collinear_parts) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing collinear facts in premise",
                        details="Vertical angle theorem requires two collinear facts"
                    ))

                collinear_matches = [re.match(r'Collinear\((\w+)\)', part) for part in collinear_parts]
                if not all(collinear_matches):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Invalid collinear fact format",
                        details="Expected Collinear(XXX)"
                    ))

                collinear_points = [m.group(1) for m in collinear_matches if m]

                # Verify each collinear fact exists in the system
                for points in collinear_points:
                    normalized = self.normalize_collinear_points(points)
                    if not any(self.normalize_collinear_points(''.join(fact)) == normalized
                               for fact in self.collinear_facts):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Collinear fact for {points} not established",
                            details=f"Known collinear facts: {[''.join(p) for p in self.collinear_facts]}"
                        ))

                # Check that the collinear lines intersect at the angle vertex
                # For vertical angles, both angles must share the same vertex (middle point)
                if angle1[1] != angle2[1]:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Angles do not share a common vertex",
                        details=f"Angles {angle1} and {angle2} must have the same middle point for vertical angles"
                    ))

                # Common vertex (intersection point)
                common_vertex = angle1[1]

                # Verify common vertex is in both collinear lines
                if not all(common_vertex in points for points in collinear_points):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Vertex {common_vertex} not in both collinear lines",
                        details="The angle vertex must be the intersection point of the lines"
                    ))

                # Verify angle facts
                angle_parts = [p for p in premise_parts if p.startswith("Angle")]
                if len(angle_parts) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing angle facts in premise",
                        details="Vertical angle theorem requires two angle facts"
                    ))

                # Check that the specified angles are in the angle parts
                if not any(p == f"Angle({angle1})" for p in angle_parts):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Angle fact for {angle1} missing in premise",
                        details=f"Expected Angle({angle1})"
                    ))

                if not any(p == f"Angle({angle2})" for p in angle_parts):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Angle fact for {angle2} missing in premise",
                        details=f"Expected Angle({angle2})"
                    ))

                # All checks passed
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for vertical_angle"
                ))



        elif theorem_name == "isosceles_triangle_judgment_angle_equal":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing triangle argument for isosceles_triangle_judgment_angle_equal",
                        details="Expected isosceles_triangle_judgment_angle_equal(1, triangle)"
                    ))

                triangle = args[1].strip()  # e.g., "ABE"

                # Parse premise parts
                premise_parts = premise.split('&')

                # First check if the polygon exists in our stored polygons
                polygon_part = premise_parts[0].strip()
                polygon_match = re.match(r'Polygon\((\w+)\)', polygon_part)

                if not polygon_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing or invalid polygon fact in premise",
                        details="Expected Polygon(...) in premise"
                    ))

                polygon_name = polygon_match.group(1)
                if polygon_name != triangle:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Polygon in premise ({polygon_name}) doesn't match triangle in theorem call ({triangle})",
                        details="Polygon and triangle argument must match"
                    ))

                # Check if this polygon is defined in our system
                norm_triangle = self.normalize_triangle(triangle)
                if norm_triangle not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Polygon {triangle} is not defined in the system",
                        details="The construction data did not define this polygon"
                    ))

                # Check for the angle equality in the premise
                if len(premise_parts) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing angle equality in premise",
                        details="Expected Equal(MeasureOfAngle(...),MeasureOfAngle(...)) in premise"
                    ))

                angle_equality = premise_parts[1].strip()
                angle_match = re.match(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)',
                                       angle_equality)

                if not angle_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Invalid angle equality format in premise",
                        details="Expected Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY)) format"
                    ))

                angle1, angle2 = angle_match.groups()

                # Verify that this angle equality actually holds in our current constraints
                if not self.check_angle_equality(angle1, angle2):
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Angles {angle1} and {angle2} are not proven equal in the system",
                        details="The current constraints don't force these angles to be equal"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for isosceles_triangle_judgment_angle_equal"
                ))

        elif theorem_name == "parallelogram_judgment_parallel_and_parallel":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing quadrilateral name for parallelogram_judgment_parallel_and_parallel",
                        details="Expected parallelogram_judgment_parallel_and_parallel(1, quadrilateral)"
                    ))

                quad_name = args[1].strip()  # e.g., "BCDF"

                # Parse the premise parts
                premise_parts = premise.split('&')

                # First check if the polygon exists in our system
                polygon_part = premise_parts[0].strip() if premise_parts else ""
                polygon_match = re.match(r'Polygon\((\w+)\)', polygon_part)

                if not polygon_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing polygon fact in premise",
                        details="Expected Polygon(...) in premise"
                    ))

                polygon_name = polygon_match.group(1)
                if polygon_name != quad_name:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Polygon in premise ({polygon_name}) doesn't match quadrilateral in theorem call ({quad_name})",
                        details="Polygon and quadrilateral argument must match"
                    ))

                # Check if this polygon is defined in our system
                if quad_name not in self.polygons and ''.join(sorted(quad_name)) not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Polygon {quad_name} is not defined in the system",
                        details="Cannot verify parallelogram properties for undefined polygon"
                    ))

                # Check for the two parallel line statements
                if len(premise_parts) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing parallel side conditions",
                        details="Need two ParallelBetweenLine statements in premise"
                    ))

                # Parse each parallel statement
                for i, part in enumerate(premise_parts[1:3], 1):
                    parallel_match = re.match(r'ParallelBetweenLine\((\w+),(\w+)\)', part.strip())
                    if not parallel_match:
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Invalid parallel line format in premise part {i + 1}",
                            details=f"Expected ParallelBetweenLine(XX,YY) but got {part}"
                        ))

                    # Extract the two lines
                    line1, line2 = parallel_match.groups()

                    # Verify this parallel relationship is already established
                    possible_pairs = [
                        (line1, line2),
                        (line2, line1),
                        (line1[::-1], line2),
                        (line1, line2[::-1]),
                        (line1[::-1], line2[::-1]),
                        (line2[::-1], line1),
                        (line2, line1[::-1]),
                        (line2[::-1], line1[::-1])
                    ]

                    if not any(pair in self.parallel_pairs for pair in possible_pairs):
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Parallel relationship between {line1} and {line2} not established",
                            details=f"Known parallel pairs: {self.parallel_pairs}"
                        ))

                # Verify the two lines form opposite sides of the quadrilateral
                # This is a more complex check that would require analyzing the quadrilateral structure
                # For simplicity, we'll skip this check for now

                return True, None
            elif version == "2":
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Version 2 for parallelogram_judgment_parallel_and_parallel not implemented"
                ))




        elif theorem_name == "perpendicular_bisector_property_distance_equal":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Insufficient arguments for perpendicular_bisector_property_distance_equal",
                        details="Expected format: perpendicular_bisector_property_distance_equal(1, bisector, bisected)"
                    ))

                bisector = args[1].strip()  # e.g., "EF"
                bisected = args[2].strip()  # e.g., "AC"

                # Check if the perpendicular bisector relationship is established
                relationship_exists = False

                if hasattr(self, "perpendicular_bisectors"):
                    # Check all variations
                    bisector_variations = [bisector, bisector[::-1]]
                    bisected_variations = [bisected, bisected[::-1]]

                    for b1 in bisector_variations:
                        for b2 in bisected_variations:
                            if (b1, b2) in self.perpendicular_bisectors:
                                relationship_exists = True
                                break
                        if relationship_exists:
                            break

                if not relationship_exists:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Perpendicular bisector relationship not established: {bisector} is not a perpendicular bisector of {bisected}",
                        details="Required for perpendicular_bisector_property_distance_equal theorem"
                    ))

                # All checks passed
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for perpendicular_bisector_property_distance_equal"
                ))


        elif theorem_name == "triangle_area_formula_common":
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing triangle name for triangle_area_formula_common",
                        details="Expected triangle_area_formula_common(1, triangle)"
                    ))

                triangle = args[1].strip()  # e.g., "DCA"

                # Check if the polygon exists in stored data
                normalized_triangle = self.normalize_triangle(triangle)
                if normalized_triangle not in self.polygons:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Triangle {triangle} not defined in the geometric data",
                        details=f"Known polygons: {self.polygons}"
                    ))

                # Check if a height has been established for this triangle
                if hasattr(self, "triangle_heights") and triangle not in self.triangle_heights:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"No height established for triangle {triangle}",
                        details="Height must be established through an altitude theorem first"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for triangle_area_formula_common"
                ))


        elif theorem_name == "altitude_of_triangle_judgment":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Insufficient arguments for altitude_of_triangle_judgment",
                        details="Expected format: altitude_of_triangle_judgment(1, altitude_line, triangle)"
                    ))

                altitude_line = args[1].strip()  # e.g., "DN"
                triangle = args[2].strip()  # e.g., "DAB"

                # Parse the premise parts
                premise_parts = premise.split('&')

                # Check for polygon fact
                polygon_found = False
                polygon_match = re.search(r'Polygon\((\w+)\)', premise)
                if polygon_match:
                    polygon_name = polygon_match.group(1)
                    normalized_polygon = self.normalize_triangle(polygon_name)
                    if normalized_polygon in self.polygons:
                        polygon_found = True
                        if normalized_polygon != self.normalize_triangle(triangle):
                            return return_error(GeometricError(
                                tier=ErrorTier.TIER2_PREMISE,
                                message=f"Polygon in premise ({polygon_name}) doesn't match the triangle in theorem call ({triangle})",
                                details="Polygon and triangle argument must match"
                            ))

                if not polygon_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing valid polygon fact in premise",
                        details="altitude_of_triangle_judgment requires a valid Polygon fact"
                    ))

                # Check for line fact
                line_found = False
                for part in premise_parts:
                    if part.startswith("Line(") and altitude_line in part:
                        line_found = True
                        break

                if not line_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Missing line fact for {altitude_line}",
                        details="altitude_of_triangle_judgment requires a Line fact for the altitude"
                    ))

                # Check for collinearity fact (for the foot of the altitude)
                collinear_found = False
                collinear_match = re.search(r'Collinear\((\w+)\)', premise)
                if collinear_match:
                    collinear_points = collinear_match.group(1)
                    # Check if any stored collinear fact matches this
                    for fact in self.collinear_facts:
                        fact_str = ''.join(fact)
                        if all(p in fact_str for p in collinear_points):
                            collinear_found = True
                            break

                if not collinear_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing valid collinearity fact in premise",
                        details="altitude_of_triangle_judgment requires a valid Collinear fact"
                    ))

                # Check for right angle fact
                right_angle_found = False
                angle_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),90\)', premise)
                if angle_match:
                    angle_name = angle_match.group(1)
                    angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

                    # Check if this angle is constrained to be 90 degrees
                    temp_solver = Solver()
                    for c in self.solver.assertions():
                        temp_solver.add(c)

                    temp_solver.add(angle_var != 90)
                    if temp_solver.check() == unsat:
                        right_angle_found = True

                if not right_angle_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing valid right angle fact in premise",
                        details="altitude_of_triangle_judgment requires an angle equal to 90 degrees"
                    ))

                # All checks passed
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for altitude_of_triangle_judgment"
                ))

        elif theorem_name == "flat_angle":
            # Expected arguments: version, angle
            version = args[0]
            if version == "1":
                if len(args) < 2:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Insufficient arguments for flat_angle",
                        details="Expected format: flat_angle(1, angle)"
                    ))

                angle_name = args[1].strip()  # e.g., "BPA"

                # Check that the three points are collinear
                collinear_found = False

                # Normalize the angle points to match how collinearity is stored
                points = list(angle_name)  # Convert "BPA" to ['B', 'P', 'A']

                for fact in self.collinear_facts:
                    # Convert fact list to string for comparison
                    fact_str = ''.join(fact)

                    # Check if all points from the angle are in this collinear fact
                    if all(p in fact_str for p in points):
                        collinear_found = True
                        break

                if not collinear_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Points {angle_name} are not proven collinear",
                        details="Required collinearity for flat_angle theorem is not established"
                    ))

                # All checks passed
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for flat_angle"
                ))




        elif theorem_name == "circle_property_circular_power_chord_and_chord":

            version = args[0]

            if version == "1":

                if len(args) < 4:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Insufficient arguments for circle_property_circular_power_chord_and_chord",

                        details="Expected format: circle_property_circular_power_chord_and_chord(1, chord1, chord2, circle)"

                    ))

                chord1 = args[1].strip()  # e.g., "BEA"

                chord2 = args[2].strip()  # e.g., "DEC"

                circle_token = args[3].strip()  # e.g., "F"

                # Count how many points from each chord are on the circle

                chord1_points_on_circle = []

                chord2_points_on_circle = []

                for point in chord1:

                    for fact in self.cocircular_facts:

                        if fact[0] == circle_token and point in fact[1:]:
                            chord1_points_on_circle.append(point)

                            break

                for point in chord2:

                    for fact in self.cocircular_facts:

                        if fact[0] == circle_token and point in fact[1:]:
                            chord2_points_on_circle.append(point)

                            break

                # We need at least 2 points from each chord to be on the circle

                if len(chord1_points_on_circle) < 2:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"Not enough points from chord {chord1} are on circle {circle_token}",

                        details=f"Found only points {chord1_points_on_circle} on circle {circle_token}, need at least 2"

                    ))

                if len(chord2_points_on_circle) < 2:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"Not enough points from chord {chord2} are on circle {circle_token}",

                        details=f"Found only points {chord2_points_on_circle} on circle {circle_token}, need at least 2"

                    ))

                # Check for collinearity facts in the stored collinear_facts

                collinear1_found = False

                collinear2_found = False

                # Normalize the chord strings to match how collinearity is stored

                norm_chord1 = self.normalize_collinear_points(chord1)

                norm_chord2 = self.normalize_collinear_points(chord2)

                for fact in self.collinear_facts:

                    # Convert fact list to string for comparison

                    fact_str = ''.join(fact)

                    # Normalize for comparison

                    norm_fact = self.normalize_collinear_points(fact_str)

                    # Check if all points from the chord are in this fact

                    if all(p in norm_fact for p in norm_chord1):
                        collinear1_found = True

                    if all(p in norm_fact for p in norm_chord2):
                        collinear2_found = True

                if not collinear1_found:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"Missing collinearity fact for points in {chord1}",

                        details=f"Points {chord1} must be collinear"

                    ))

                if not collinear2_found:
                    return return_error(GeometricError(

                        tier=ErrorTier.TIER2_PREMISE,

                        message=f"Missing collinearity fact for points in {chord2}",

                        details=f"Points {chord2} must be collinear"

                    ))

                # All checks passed

                return True, None

            else:

                return return_error(GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message=f"Unsupported version {version} for circle_property_circular_power_chord_and_chord"

                ))


        elif theorem_name == "round_angle":
            # Expected arguments: version, angle1, angle2
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Insufficient arguments for round_angle",
                        details="Expected format: round_angle(1, angle1, angle2)"
                    ))

                angle1 = args[1].strip()  # e.g., "FBC"
                angle2 = args[2].strip()  # e.g., "CBF"

                # Check if both angles exist in our system
                normalized_angle1 = self.normalize_angle_name(angle1)
                normalized_angle2 = self.normalize_angle_name(angle2)

                angle1_var_name = f"angle_{normalized_angle1}"
                angle2_var_name = f"angle_{normalized_angle2}"

                if angle1_var_name not in self.angles:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Angle {angle1} is not defined",
                        details="Required angle for round_angle theorem is not established"
                    ))

                if angle2_var_name not in self.angles:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Angle {angle2} is not defined",
                        details="Required angle for round_angle theorem is not established"
                    ))

                # All checks passed
                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for round_angle"
                ))




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

            if self.normalize_triangle(tri) not in self.polygons:
                return return_error(GeometricError(

                    tier=ErrorTier.TIER2_PREMISE,

                    message=f"Polygon for triangle {tri} is missing",

                    details="The construction data did not define this polygon."

                ))

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
                # if not polygon_found:
                #     return return_error(GeometricError(
                #         tier=ErrorTier.TIER2_PREMISE,
                #         message=f"Polygon fact for triangle {triangle} is missing in the premise.",
                #         details=f"Premise provided: {premise}"
                #     ))
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

            feedback = ""
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

                        # If there are more than 3 points, break it down into all possible 3-point combinations
                        if len(points) > 3:
                            from itertools import combinations
                            for sub_points in combinations(points, 3):
                                three_points = ''.join(sub_points)
                                normalized_points = self.normalize_collinear_points(three_points)
                                normalized_str = ''.join(normalized_points)

                                # If the same fact appears in the main CONSTRUCTION_CDL section, skip it
                                if normalized_str in normal_collinear_set:
                                    print(
                                        f"Skipping duplicate collinear fact from extended section: {normalized_points}")
                                    continue

                                # Otherwise, add it
                                self.collinear_facts.append(list(normalized_points))
                                self.add_collinear_fact(list(normalized_points))
                                print(f"Added normalized collinear points (extended): {normalized_points}")
                        else:
                            # Original behavior for 3 or fewer points
                            normalized_points = self.normalize_collinear_points(points)
                            normalized_str = ''.join(normalized_points)

                            # If the same fact appears in the main CONSTRUCTION_CDL section, skip it
                            if normalized_str in normal_collinear_set:
                                print(f"Skipping duplicate collinear fact from extended section: {normalized_points}")
                                continue

                            # Otherwise, add it
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

                            # Add side equality constraints for the rhombus

                            if len(shape_name) >= 4:  # Ensure we have at least 4 vertices

                                # Extract all adjacent vertex pairs (sides of the rhombus)

                                sides = []

                                for i in range(len(shape_name)):
                                    side = shape_name[i] + shape_name[(i + 1) % len(shape_name)]

                                    sides.append(side)

                                # Create length variables for all sides

                                side_vars = []

                                for side in sides:
                                    side_var = self.add_length(side[0], side[1])

                                    side_vars.append(side_var)

                                # Add constraints that all sides are equal to each other

                                for i in range(1, len(side_vars)):
                                    self.solver.add(side_vars[0] == side_vars[i])

                                print(f"Added rhombus side equality constraints for {shape_name}: {' = '.join(sides)}")





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
                        angle_equality_match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\)',
                                                        line)

                        if angle_equality_match:
                            angle1, angle2 = angle_equality_match.group(1), angle_equality_match.group(2)
                            print(f"Found angle equality in TEXT_CDL: {angle1} = {angle2}")

                            # Get or create the Z3 variables for both angles
                            angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                            angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                            # Add constraint that they are equal
                            self.solver.add(angle1_var == angle2_var)
                            print(f"Added angle equality constraint: {angle1} = {angle2}")

                        else:
                            # If not an angle = angle pattern, try the original angle = value pattern
                            value_match = re.match(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                            if value_match:
                                angle_name, expression = value_match.group(1), value_match.group(2).strip()
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


                    elif line.startswith('CongruentBetweenTriangle('):

                        match = re.match(r'CongruentBetweenTriangle\((\w+),(\w+)\)', line)

                        if match:

                            tri1, tri2 = match.groups()

                            canonical_pair = self.canonicalize_congruent_triangle_pair(tri1, tri2)

                            if not hasattr(self, "congruent_triangles"):
                                self.congruent_triangles = []

                            if canonical_pair not in self.congruent_triangles:
                                self.congruent_triangles.append(canonical_pair)

                            print(f"Added congruent triangles: {tri1} and {tri2} (canonical: {canonical_pair})")

                    elif line.startswith('Equal(PerimeterOfTriangle('):
                        # Match pattern like: Equal(PerimeterOfTriangle(OCD),23)
                        perimeter_match = re.match(r'Equal\(PerimeterOfTriangle\((\w+)\),(.+)\)', line)
                        if perimeter_match:
                            triangle_name, perimeter_value = perimeter_match.groups()
                            perimeter_value = perimeter_value.strip()
                            print(
                                f"Found triangle perimeter in TEXT_CDL: PerimeterOfTriangle({triangle_name}) = {perimeter_value}")

                            # Initialize triangle_perimeters if it doesn't exist
                            if not hasattr(self, 'triangle_perimeters'):
                                self.triangle_perimeters = {}

                            # Create perimeter variable if not already created
                            if triangle_name not in self.triangle_perimeters:
                                perimeter_var = Real(f"perimeter_{triangle_name}")
                                self.triangle_perimeters[triangle_name] = perimeter_var
                            else:
                                perimeter_var = self.triangle_perimeters[triangle_name]

                            # Parse perimeter value and add constraint
                            try:
                                # Try parsing as numeric value
                                import math
                                eval_env = {"sqrt": math.sqrt, "pi": math.pi}
                                value = float(eval(perimeter_value, {"__builtins__": {}}, eval_env))
                                self.solver.add(perimeter_var == value)
                                print(
                                    f"Added numeric perimeter constraint: PerimeterOfTriangle({triangle_name}) = {value}")

                                # Define perimeter as sum of sides
                                # For triangle ABC, sides are AB, BC, and CA
                                if len(triangle_name) == 3:
                                    # Create length variables for each side
                                    side1_var = self.add_length(triangle_name[0], triangle_name[1])
                                    side2_var = self.add_length(triangle_name[1], triangle_name[2])
                                    side3_var = self.add_length(triangle_name[2], triangle_name[0])

                                    # Define perimeter as sum of sides
                                    self.solver.add(perimeter_var == side1_var + side2_var + side3_var)
                                    print(f"Added perimeter definition: PerimeterOfTriangle({triangle_name}) = "
                                          f"LengthOfLine({triangle_name[0]}{triangle_name[1]}) + "
                                          f"LengthOfLine({triangle_name[1]}{triangle_name[2]}) + "
                                          f"LengthOfLine({triangle_name[2]}{triangle_name[0]})")
                            except Exception as e:
                                print(f"Could not evaluate as numeric: {perimeter_value}. Error: {e}")
                                # Handle algebraic expression if needed
                                variables = self.extract_variables(perimeter_value)
                                for var in variables:
                                    if var not in self.variables:
                                        self.variables[var] = Real(var)
                                        print(f"Created new variable for algebraic perimeter: {var}")
                                expr = self.parse_algebraic_expression(perimeter_value)
                                self.solver.add(perimeter_var == expr)
                                print(
                                    f"Added algebraic perimeter constraint: PerimeterOfTriangle({triangle_name}) = {expr}")

                    elif line.startswith('IsBisectorOfAngle('):
                        match = re.match(r'IsBisectorOfAngle\((\w+),(\w+)\)', line)
                        if match:
                            bisector_line, angle = match.groups()
                            print(f"Found angle bisector in TEXT_CDL: {bisector_line} bisects {angle}")

                            # Extract the three vertices of the angle
                            if len(angle) != 3:
                                print(f"Warning: Expected angle to have 3 vertices, but got {angle}")
                                continue

                            # Angle is specified as XYZ where Y is the vertex
                            # Bisector is specified as YO where Y is the vertex and O is some point
                            vertex = angle[1]

                            # Check if the bisector includes the vertex
                            if bisector_line[0] != vertex and bisector_line[1] != vertex:
                                print(f"Warning: Bisector {bisector_line} doesn't appear to include vertex {vertex}")
                                continue

                            # Extract the bisector point (not the vertex)
                            bisector_point = bisector_line[1] if bisector_line[0] == vertex else bisector_line[0]

                            # Form the two angles that should be equal
                            # If the angle is ABC and the bisector is BO, then ABO = CBO
                            first_point = angle[0]
                            third_point = angle[2]

                            angle1 = f"{first_point}{vertex}{bisector_point}"
                            angle2 = f"{third_point}{vertex}{bisector_point}"

                            # Normalize angle names
                            norm_angle1 = self.normalize_angle_name(angle1)
                            norm_angle2 = self.normalize_angle_name(angle2)

                            # Get or create the Z3 variables for both angles
                            angle1_var = self.add_angle(norm_angle1[0], norm_angle1[1], norm_angle1[2])
                            angle2_var = self.add_angle(norm_angle2[0], norm_angle2[1], norm_angle2[2])

                            # Add constraint that they are equal
                            self.solver.add(angle1_var == angle2_var)
                            print(f"Added angle bisector constraint: {norm_angle1} = {norm_angle2}")

                            # Store the bisector fact for later reference if needed
                            if not hasattr(self, 'angle_bisectors'):
                                self.angle_bisectors = []
                            self.angle_bisectors.append((bisector_line, angle))



                    elif line.startswith('IsAltitudeOfTriangle('):
                        match = re.match(r'IsAltitudeOfTriangle\((\w+),(\w+)\)', line)
                        if match:
                            altitude_line, triangle = match.groups()
                            print(
                                f"Found triangle altitude in TEXT_CDL: {altitude_line} is altitude of triangle {triangle}")

                            # Extract vertices - altitude line should start from one vertex of the triangle
                            # and end at a point on the opposite side
                            if len(triangle) != 3 or len(altitude_line) != 2:
                                print(f"Warning: Invalid format. Expected 3-vertex triangle and 2-point altitude line")
                                continue

                            # Find which vertex of the triangle is the start of the altitude
                            vertex = None
                            for v in triangle:
                                if v in altitude_line:
                                    vertex = v
                                    break

                            if vertex is None:
                                print(
                                    f"Warning: Altitude {altitude_line} doesn't start from any vertex of triangle {triangle}")
                                continue

                            # Find the endpoint of the altitude (the point not in the triangle vertices)
                            endpoint = altitude_line[0] if altitude_line[1] == vertex else altitude_line[1]

                            # Find the two vertices forming the opposite side
                            opposite_vertices = [v for v in triangle if v != vertex]
                            if len(opposite_vertices) != 2:
                                print(f"Warning: Could not identify opposite side for altitude {altitude_line}")
                                continue

                            # For BE altitude in triangle BCA, we need angle BEC = 90°
                            # Create angle variables for both possible orientations of the perpendicular angle
                            angle1 = f"{vertex}{endpoint}{opposite_vertices[0]}"
                            angle2 = f"{vertex}{endpoint}{opposite_vertices[1]}"

                            # Normalize angle names
                            norm_angle1 = self.normalize_angle_name(angle1)
                            norm_angle2 = self.normalize_angle_name(angle2)

                            # Add 90 degree constraints for both angles
                            angle1_var = self.add_angle(norm_angle1[0], norm_angle1[1], norm_angle1[2])
                            self.solver.add(angle1_var == 90)
                            print(f"Added altitude perpendicular constraint: {norm_angle1} = 90°")

                            # We don't need to add constraints for both angles if they're the same normalized angle
                            if norm_angle1 != norm_angle2:
                                angle2_var = self.add_angle(norm_angle2[0], norm_angle2[1], norm_angle2[2])
                                self.solver.add(angle2_var == 90)
                                print(f"Added altitude perpendicular constraint: {norm_angle2} = 90°")

                            # Store the altitude fact for later reference
                            if not hasattr(self, 'triangle_altitudes'):
                                self.triangle_altitudes = []
                            self.triangle_altitudes.append((altitude_line, triangle))


                    elif line.startswith("IsPerpendicularBisectorOfLine("):
                        # Match a statement like: IsPerpendicularBisectorOfLine(EF,AC)
                        match = re.match(r'IsPerpendicularBisectorOfLine\((\w+),(\w+)\)', line)
                        if match:
                            bisector, bisected = match.groups()  # e.g., "EF", "AC"
                            print(f"Found perpendicular bisector: {bisector} is perpendicular bisector of {bisected}")

                            # Initialize perpendicular_bisectors attribute if it doesn't exist
                            if not hasattr(self, "perpendicular_bisectors"):
                                self.perpendicular_bisectors = set()
                            bisector_variations = [bisector, bisector[::-1]]

                            # For bisected AC, add (EF,AC), (EF,CA)
                            bisected_variations = [bisected, bisected[::-1]]

                            # Add all combinations
                            for b1 in bisector_variations:
                                for b2 in bisected_variations:
                                    self.perpendicular_bisectors.add((b1, b2))

                            print(f"Added perpendicular bisector relationships: {self.perpendicular_bisectors}")
                            # Find the intersection point (e.g., point on both bisector and bisected)
                            bisector_point = None  # This will be the intersection point

                            # Check all collinear facts to find where the lines meet
                            for fact in self.collinear_facts:
                                fact_str = ''.join(fact)
                                # Look for a point that's in both the bisector and a collinear fact with the bisected line
                                for point in bisector:
                                    if point in fact_str and all(p in fact_str for p in bisected):
                                        bisector_point = point
                                        break
                                if bisector_point:
                                    break

                            if not bisector_point:
                                # Try to infer the intersection point - look for a common point in both bisector and bisected
                                common_points = set(bisector).intersection(set(bisected))
                                if common_points:
                                    bisector_point = list(common_points)[0]
                                    print(f"Inferred intersection point: {bisector_point}")
                                else:
                                    print(
                                        f"Warning: Could not find the intersection point for perpendicular bisector {bisector} of {bisected}")
                                    continue  # Skip this statement

                            # Get the two parts of the bisected line
                            parts = [p for p in bisected]

                            # Add equal distance constraints for the two parts
                            # If bisected is AC and bisector_point is E, this adds AE = EC
                            dist1 = self.add_length(bisector_point, parts[0])
                            dist2 = self.add_length(bisector_point, parts[1])
                            self.solver.add(dist1 == dist2)
                            print(
                                f"Added equal distance constraint: {bisector_point}{parts[0]} = {bisector_point}{parts[1]}")

                            # Add right angle constraints
                            # If bisector is EF, get the other point (F)
                            other_point = next(p for p in bisector if p != bisector_point)

                            # Get collinear points for the intersection point
                            collinear_points = None
                            for fact in self.collinear_facts:
                                if bisector_point in fact:
                                    collinear_points = fact
                                    break

                            if collinear_points:
                                # Add right angle for points on the collinear line
                                for p in collinear_points:
                                    if p != bisector_point and p in bisected:  # Only for the endpoints of the bisected line
                                        angle = self.add_angle(other_point, bisector_point, p)  # e.g., FEA and FEC
                                        self.solver.add(angle == 90)
                                        print(f"Added 90° angle constraint for ∠{other_point}{bisector_point}{p}")
                            else:
                                # If no collinearity fact exists, still add right angles for the bisected endpoints
                                for p in parts:
                                    angle = self.add_angle(other_point, bisector_point, p)  # e.g., FEA and FEC
                                    self.solver.add(angle == 90)
                                    print(f"Added 90° angle constraint for ∠{other_point}{bisector_point}{p}")

                            # Also add collinearity for the three key points if not already present
                            bisected_with_bisector_point = parts[0] + bisector_point + parts[1]
                            normalized_collinear = self.normalize_collinear_points(bisected_with_bisector_point)

                            # Check if this collinearity is already recorded
                            collinear_exists = False
                            for fact in self.collinear_facts:
                                fact_str = self.normalize_collinear_points(''.join(fact))
                                if normalized_collinear == fact_str:
                                    collinear_exists = True
                                    break

                            if not collinear_exists:
                                # Add new collinearity fact
                                self.collinear_facts.append(list(normalized_collinear))
                                self.add_collinear_fact(list(normalized_collinear))
                                print(f"Added collinearity fact for {normalized_collinear}")

                            print(
                                f"Processed perpendicular bisector: {bisector_point} divides {bisected} equally with right angles")

                    elif line.startswith("Equal(AreaOfTriangle("):

                        # Parse text like: Equal(AreaOfTriangle(ABC),65) or Equal(AreaOfTriangle(ABC),Add(AreaOfTriangle(DCA),AreaOfTriangle(DAB)))

                        full_match = re.match(r'Equal\(AreaOfTriangle\((\w+)\),(.*)\)', line)

                        if full_match:

                            triangle, expression = full_match.groups()

                            expression = expression.strip()

                            # Normalize the primary triangle name

                            normalized_triangle = ''.join(sorted(triangle))

                            print(f"Found triangle area: AreaOfTriangle({triangle}) = {expression}")

                            # Create or get the primary triangle area variable

                            if normalized_triangle not in self.triangle_areas:
                                self.triangle_areas[normalized_triangle] = Real(f"areaTriangle_{normalized_triangle}")

                                self.solver.add(self.triangle_areas[normalized_triangle] >= 0)

                                print(f"Created triangle area variable: areaTriangle_{normalized_triangle}")

                            area_var = self.triangle_areas[normalized_triangle]

                            # Parse the right side based on its format

                            if expression.startswith("Add(AreaOfTriangle("):

                                # Debug output

                                print(f"Detected triangle addition expression: {expression}")

                                # Special case for Add(AreaOfTriangle(...),AreaOfTriangle(...))

                                # Find both triangles in the addition formula

                                triangle_pattern = r'AreaOfTriangle\((\w+)\)'

                                add_triangles = re.findall(triangle_pattern, expression)

                                # Debug output

                                print(f"Found triangles in addition: {add_triangles}")

                                if len(add_triangles) >= 2:

                                    # We have at least two triangles in the addition

                                    tri1, tri2 = add_triangles  # First two triangles

                                    # Normalize triangle names

                                    norm_tri1 = ''.join(sorted(tri1))

                                    norm_tri2 = ''.join(sorted(tri2))

                                    # Create variables for the summed triangles

                                    if norm_tri1 not in self.triangle_areas:
                                        self.triangle_areas[norm_tri1] = Real(f"areaTriangle_{norm_tri1}")

                                        self.solver.add(self.triangle_areas[norm_tri1] >= 0)

                                        print(f"Created triangle area variable: areaTriangle_{norm_tri1}")

                                    if norm_tri2 not in self.triangle_areas:
                                        self.triangle_areas[norm_tri2] = Real(f"areaTriangle_{norm_tri2}")

                                        self.solver.add(self.triangle_areas[norm_tri2] >= 0)

                                        print(f"Created triangle area variable: areaTriangle_{norm_tri2}")

                                    # Set up the addition constraint

                                    tri1_var = self.triangle_areas[norm_tri1]

                                    tri2_var = self.triangle_areas[norm_tri2]

                                    self.solver.add(area_var == tri1_var + tri2_var)

                                    print(f"Added constraint: Area({triangle}) = Area({tri1}) + Area({tri2})")

                                    print(f"Current triangle areas: {list(self.triangle_areas.keys())}")

                                else:

                                    print(f"WARNING: Could not extract triangles from addition: {expression}")

                            else:

                                # Handle numeric or algebraic expression as before

                                try:

                                    import math

                                    eval_env = {"sqrt": math.sqrt, "pi": math.pi}

                                    value = float(eval(expression, {"__builtins__": {}}, eval_env))

                                    self.solver.add(area_var == value)

                                    print(f"Added numeric triangle area constraint: Area({triangle}) = {value}")

                                except Exception as e:

                                    print(f"Could not evaluate as numeric: {expression}. Error: {e}")

                                    # Handle as algebraic expression

                                    variables = self.extract_variables(expression)

                                    for var in variables:

                                        if var not in self.variables:
                                            self.variables[var] = Real(var)

                                            print(f"Created new variable for algebraic area: {var}")

                                    expr = self.parse_algebraic_expression(expression)

                                    self.solver.add(area_var == expr)

                                    print(f"Added algebraic triangle area constraint: Area({triangle}) = {expr}")

                    elif line.startswith("IsMidpointOfLine("):
                        # Matches a fact like: IsMidpointOfLine(C,AO)
                        match = re.match(r'IsMidpointOfLine\((\w+),(\w+)\)', line)
                        if match:
                            midpoint, segment = match.groups()

                            # Make sure segment is a 2-character string representing the endpoints
                            if len(segment) != 2:
                                print(f"Error: Invalid segment format in IsMidpointOfLine({midpoint},{segment})")
                                continue

                            # Initialize midpoint tracking if not already present
                            if not hasattr(self, "midpoints"):
                                self.midpoints = {}

                            # Record the midpoint relationship
                            self.midpoints[(segment[0], segment[1])] = midpoint
                            # Also record the reverse order
                            self.midpoints[(segment[1], segment[0])] = midpoint

                            # Add the midpoint constraints to the solver:
                            # 1. The distance from first endpoint to midpoint equals distance from midpoint to second endpoint
                            # 2. The midpoint is on the line between the endpoints

                            # Get length variables for both half-segments
                            len1 = self.add_length(segment[0], midpoint)
                            len2 = self.add_length(midpoint, segment[1])

                            # Add equality constraint: AC = CB
                            self.solver.add(len1 == len2)

                            # Also add collinearity constraint if we track that explicitly
                            if not any(set([segment[0], midpoint, segment[1]]).issubset(set(''.join(fact))) for fact in
                                       self.collinear_facts):
                                collinear_points = [segment[0], midpoint, segment[1]]
                                normalized_points = self.normalize_collinear_points(''.join(collinear_points))
                                self.collinear_facts.append(list(normalized_points))
                                self.add_collinear_fact(list(normalized_points))
                                print(
                                    f"Added collinearity constraint for midpoint: {segment[0]}, {midpoint}, {segment[1]}")

                            print(f"Recorded midpoint: {midpoint} is the midpoint of segment {segment[0]}{segment[1]}")
                        else:
                            print("Error parsing IsMidpointOfLine fact in TEXT_CDL.")

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
                        match = re.match(r'Equal\(Div\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\),(.+)\)', line)
                        if match:
                            line1, line2, expression = match.groups()
                            expression = expression.strip()
                            print(
                                f"Found division length expression in TEXT_CDL: Div(LengthOfLine({line1}),LengthOfLine({line2})) = {expression}")

                            # Get the two length variables
                            len1 = self.add_length(line1[0], line1[1])
                            len2 = self.add_length(line2[0], line2[1])

                            # Try to parse the expression as a fraction first
                            try:
                                from fractions import Fraction
                                div_val = float(Fraction(expression))
                                print(f"Parsed division value as fraction: {div_val}")
                            except Exception as e:
                                try:
                                    # Fall back to safe evaluation with limited context
                                    div_val = float(eval(expression, {"__builtins__": {}}, {"pi": 3.141592653589793}))
                                    print(f"Parsed division value using eval: {div_val}")
                                except Exception as e2:
                                    print(f"Error parsing division value '{expression}': {str(e2)}")
                                    continue

                            # Add the division constraint (rewritten to avoid potential division by zero)
                            self.solver.add(len1 == len2 * div_val)  # Equivalent to len1/len2 == div_val
                            print(
                                f"Added division constraint: {line1} = {line2} * {div_val} (equivalent to {line1}/{line2} = {div_val})")
                        else:
                            print(f"Error: Could not parse division expression in line: {line}")
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
                                return False,f"Error in {error.tier.name}: {error.message}"


                            # Then process theorem step
                            error = self.adding_conclution(theorem_name, args, premise, conclusions)
                            if error:
                                print(f"\nError in {error.tier.name}:")
                                print(f"Message: {error.message}")
                                if error.details:
                                    print(f"Details: {error.details}")
                                return False, f"Error in {error.tier.name}: {error.message}"

            if 'GOAL_CDL' in sections:
                goal_line = sections['GOAL_CDL'][0]

                def parse_special_answer(answer_str):
                    """Parse answer strings including those with square root symbol."""
                    import math
                    import re

                    # Remove whitespace
                    answer_str = answer_str.strip()

                    # Handle √ symbol format: 6(√6-1)
                    if '√' in answer_str:
                        # Handle pattern like "6(√6-1)"
                        pattern = r'(\d+)\(√(\d+)(-|\+)(\d+)\)'
                        match = re.match(pattern, answer_str)
                        if match:
                            a, b, op, c = match.groups()
                            a, b, c = float(a), float(b), float(c)
                            if op == '-':
                                return a * (math.sqrt(b) - c)
                            else:  # op == '+'
                                return a * (math.sqrt(b) + c)

                        # General replacement of √ symbol
                        modified_str = re.sub(r'√(\d+)', r'math.sqrt(\1)', answer_str)
                        # Handle implicit multiplication
                        modified_str = re.sub(r'(\d+)\(', r'\1*(', modified_str)
                        try:
                            return float(eval(modified_str, {"math": math}))
                        except Exception:
                            pass

                    # Standard eval with math functions
                    try:
                        return float(eval(answer_str, {"pi": math.pi, "sqrt": math.sqrt}))
                    except Exception:
                        # Fall back to Fraction
                        from fractions import Fraction
                        return float(Fraction(answer_str))
                # --- Check for an arc length goal of the form:
                #     Value(LengthOfArc(X))
                # --- Check for an arc length goal of the form:
                #     Value(LengthOfArc(X))
                # --- Check for an arc measure goal of the form:
                #     Value(MeasureOfArc(X))
                arc_measure_match = re.search(r'Value\(MeasureOfArc\((\w+)\)\)', goal_line)
                if arc_measure_match:
                    arc_token = arc_measure_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected = parse_special_answer(sections['ANSWER'][0].strip())

                        print(f"\nGoal arc measure: {arc_token}")
                        print(f"Expected measure: {expected}")

                        # Get the arc variable
                        normalized_arc = self.normalize_arc(arc_token)
                        arc_var_name = f"arc_{normalized_arc}"

                        if arc_var_name in self.arcs:
                            arc_var = self.arcs[arc_var_name]

                            if self.solver.check() == sat:
                                # First check if constraints allow the expected value
                                temp_solver1 = Solver()
                                for c in self.solver.assertions():
                                    temp_solver1.add(c)

                                # Add constraint that arc_var == expected (within epsilon)
                                epsilon = 1e-8
                                temp_solver1.add(And(arc_var >= expected - epsilon, arc_var <= expected + epsilon))

                                if temp_solver1.check() != sat:
                                    error_msg = f"Failed to prove arc measure goal: constraints don't allow the expected value."

                                    # Generate detailed report for this case
                                    arc_report = self.generate_arc_length_analysis_report(arc_token, expected, None,
                                                                                          "incompatible")

                                    print(f"Error: Constraints don't allow the expected arc measure {expected}")
                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message=error_msg,
                                        details=f"Goal was: MeasureOfArc({arc_token}) = {expected}"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")

                                    # Write report to file
                                    self.write_failure_report(f"arc_measure_{arc_token}", arc_report)
                                    return False, arc_report

                                # Now check if any other value is allowed
                                temp_solver2 = Solver()
                                for c in self.solver.assertions():
                                    temp_solver2.add(c)

                                # Add constraint: arc_var != expected (outside epsilon range)
                                temp_solver2.add(Or(arc_var < expected - epsilon, arc_var > expected + epsilon))

                                if temp_solver2.check() == sat:
                                    alt_model = temp_solver2.model()
                                    alt_value = float(alt_model.eval(arc_var).as_decimal(10).rstrip('?'))

                                    error_msg = f"Failed to prove arc measure goal: constraints allow multiple values."

                                    # Generate detailed report for this case
                                    arc_report = self.generate_arc_length_analysis_report(arc_token, expected,
                                                                                          alt_value, "multiple_values")

                                    print(f"Error: The proof doesn't uniquely determine arc measure {arc_token}.")
                                    print(f"It could be {expected} but also {alt_value}")

                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message=error_msg,
                                        details=f"Goal was: MeasureOfArc({arc_token}) = {expected}, but could also be {alt_value}"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")

                                    # Write report to file
                                    self.write_failure_report(f"arc_measure_{arc_token}", arc_report)
                                    return False, arc_report

                                # Success case
                                model = self.solver.model()
                                calc_expr = model.eval(arc_var)
                                val_str = calc_expr.as_decimal(10)
                                if val_str.endswith('?'):
                                    val_str = val_str[:-1]
                                calculated_value = float(val_str)

                                print(f"Calculated arc measure for {arc_token} is {calculated_value}")
                                print(f"Success: The arc measure {arc_token} is uniquely determined to be {expected}.")
                                return True, ""
                            else:
                                error_msg = f"Failed to prove arc measure goal: solver is unsatisfiable."

                                # Generate detailed report for unsatisfiable case
                                arc_report = self.generate_arc_length_analysis_report(arc_token, expected, None,
                                                                                      "unsatisfiable")

                                print("Solver constraints unsat when verifying arc measure goal.")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal: MeasureOfArc({arc_token}) = {expected}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")

                                # Write report to file
                                self.write_failure_report(f"arc_measure_{arc_token}", arc_report)
                                return False, arc_report
                        else:
                            error_msg = f"Arc {arc_token} is not defined in the system"
                            print(f"Error: Arc {arc_token} is not defined")
                            return False, error_msg

                # --- Check for an arc length goal of the form:
                #     Value(LengthOfArc(X))
                arc_length_match = re.search(r'Value\(LengthOfArc\((\w+)\)\)', goal_line)
                if arc_length_match:
                    arc_token = arc_length_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected = parse_special_answer(sections['ANSWER'][0].strip())

                        print(f"\nGoal arc length: {arc_token}")
                        print(f"Expected arc length: {expected}")

                        # Create a detailed error report
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
                                error_msg = f"Failed to prove arc length goal: constraints don't allow the expected value."

                                # Generate detailed report for this case
                                arc_report = self.generate_arc_length_analysis_report(arc_token, expected, None,
                                                                                      "incompatible")

                                print(f"Error: Constraints don't allow the expected arc length {expected}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal was: LengthOfArc({arc_token}) = {expected}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"arc_length_{arc_token}", arc_report)
                                return False, arc_report

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

                                error_msg = f"Failed to prove arc length goal: constraints allow multiple values."

                                # Generate detailed report for this case
                                arc_report = self.generate_arc_length_analysis_report(arc_token, expected, alt_value,
                                                                                      "multiple_values")

                                print(f"Error: The proof doesn't uniquely determine arc length {arc_token}.")
                                print(f"It could be {expected} but also {alt_value}")

                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal was: LengthOfArc({arc_token}) = {expected}, but could also be {alt_value}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"arc_length_{arc_token}", arc_report)
                                return False, arc_report

                            # Success case
                            model = self.solver.model()
                            calc_expr = model.eval(arc_length_var)
                            val_str = calc_expr.as_decimal(10)
                            if val_str.endswith('?'):
                                val_str = val_str[:-1]
                            calculated_value = float(val_str)

                            print(f"Calculated arc length for {arc_token} is {calculated_value}")
                            print(f"Success: The arc length {arc_token} is uniquely determined to be {expected}.")
                            return True, ""
                        else:
                            error_msg = f"Failed to prove arc length goal: solver is unsatisfiable."

                            # Generate detailed report for unsatisfiable case
                            arc_report = self.generate_arc_length_analysis_report(arc_token, expected, None,
                                                                                  "unsatisfiable")

                            print("Solver constraints unsat when verifying arc length goal.")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message=error_msg,
                                details=f"Goal: LengthOfArc({arc_token}) = {expected}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)

                            # Write report to file
                            self.write_failure_report(f"arc_length_{arc_token}", arc_report)
                            return False, arc_report


                # --- Check for a sum-of-lengths goal of the form:
                #     Value(Add(LengthOfLine(XX),LengthOfLine(YY)))
                # --- Check for a sum-of-lengths goal of the form:
                #     Value(Add(LengthOfLine(XX),LengthOfLine(YY)))
                # --- Check for a sum-of-lengths goal of the form:
                #     Value(Add(LengthOfLine(XX),LengthOfLine(YY)))
                sum_lengths_match = re.search(r'Value\(Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)', goal_line)
                if sum_lengths_match:
                    line1 = sum_lengths_match.group(1)  # e.g., "DN"
                    line2 = sum_lengths_match.group(2)  # e.g., "DM"

                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected_answer = parse_special_answer(sections['ANSWER'][0].strip())

                        print(f"\nGoal sum of lengths: LengthOfLine({line1}) + LengthOfLine({line2})")
                        print(f"Expected answer: {expected_answer}")

                        # Get (or create) the length variables
                        len1 = self.add_length(line1[0], line1[1])
                        len2 = self.add_length(line2[0], line2[1])

                        # Create a sum expression
                        sum_expr = len1 + len2

                        if self.solver.check() == sat:
                            # First check if constraints allow the expected value
                            temp_solver1 = Solver()
                            for c in self.solver.assertions():
                                temp_solver1.add(c)

                            # Add constraint that sum_expr == expected (within epsilon)
                            epsilon = 1e-8
                            temp_solver1.add(And(sum_expr >= expected_answer - epsilon,
                                                 sum_expr <= expected_answer + epsilon))

                            if temp_solver1.check() != sat:
                                error_msg = f"Failed to prove sum of lengths goal: constraints don't allow the expected value."

                                # Generate detailed report for this case
                                sum_report = self.generate_sum_analysis_report(line1, line2, expected_answer, None,
                                                                               "incompatible")

                                print(f"Error: Constraints don't allow the expected sum {expected_answer}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal was: LengthOfLine({line1}) + LengthOfLine({line2}) = {expected_answer}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"{line1}_{line2}_sum", sum_report)
                                return False, sum_report

                            # Now check if any other value is allowed
                            temp_solver2 = Solver()
                            for c in self.solver.assertions():
                                temp_solver2.add(c)

                            # Add constraint: sum_expr != expected (outside epsilon range)
                            temp_solver2.add(Or(sum_expr < expected_answer - epsilon,
                                                sum_expr > expected_answer + epsilon))

                            if temp_solver2.check() == sat:
                                # Get an alternate model
                                alt_model = temp_solver2.model()

                                # Evaluate each line length in this alternate model
                                alt_len1 = float(alt_model.eval(len1).as_decimal(10).rstrip('?'))
                                alt_len2 = float(alt_model.eval(len2).as_decimal(10).rstrip('?'))
                                alt_sum = alt_len1 + alt_len2

                                error_msg = f"Failed to prove sum of lengths goal: constraints allow multiple values."

                                # Generate detailed report for this case
                                sum_report = self.generate_sum_analysis_report(line1, line2, expected_answer, alt_sum,
                                                                               "multiple_values")

                                print(f"Error: The proof doesn't uniquely determine the sum {line1} + {line2}.")
                                print(f"It could be {expected_answer} but also {alt_sum}")
                                print(f"Line {line1} could be {alt_len1}")
                                print(f"Line {line2} could be {alt_len2}")

                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal was: LengthOfLine({line1}) + LengthOfLine({line2}) = {expected_answer}, but could also be {alt_sum}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"{line1}_{line2}_sum", sum_report)
                                return False, sum_report

                            # Get the computed value from the model - success case
                            model = self.solver.model()

                            # Calculate the sum from individual length values
                            try:
                                val1 = float(model.eval(len1).as_decimal(10).rstrip('?'))
                                val2 = float(model.eval(len2).as_decimal(10).rstrip('?'))
                                calculated_value = val1 + val2

                                print(f"Length of {line1}: {val1}")
                                print(f"Length of {line2}: {val2}")
                                print(f"Calculated sum: {calculated_value}")

                                # Check if the calculated value matches the expected answer
                                if abs(calculated_value - expected_answer) >= epsilon:
                                    error_msg = f"Failed to prove sum of lengths goal: calculated value {calculated_value} doesn't match expected {expected_answer}."

                                    # Generate detailed report for this case
                                    sum_report = self.generate_sum_analysis_report(line1, line2, expected_answer,
                                                                                   calculated_value, "incompatible")

                                    print(
                                        f"Error: Calculated sum {calculated_value} doesn't match expected {expected_answer}")
                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message=error_msg,
                                        details=f"Goal was: LengthOfLine({line1}) + LengthOfLine({line2}) = {expected_answer}, calculated: {calculated_value}"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")
                                    if error.details:
                                        print("Details:", error.details)

                                    # Write report to file
                                    self.write_failure_report(f"{line1}_{line2}_sum", sum_report)
                                    return False, sum_report

                                print(
                                    f"Success: The sum of lengths {line1} + {line2} is uniquely determined to be {expected_answer}.")
                                return True, ""
                            except Exception as e:
                                error_msg = f"Error calculating sum of lengths: {str(e)}"

                                # Generate detailed report for this case
                                sum_report = self.generate_sum_analysis_report(line1, line2, expected_answer, None,
                                                                               "incompatible")
                                sum_report += f"\nERROR: {str(e)}\n"

                                print(f"Error calculating sum of lengths: {e}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=str(e)
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"{line1}_{line2}_sum", sum_report)
                                return False, sum_report
                        else:
                            error_msg = f"Failed to prove sum of lengths goal: solver is unsatisfiable."

                            # Generate detailed report for unsatisfiable case
                            sum_report = self.generate_sum_analysis_report(line1, line2, expected_answer, None,
                                                                           "unsatisfiable")

                            print("Solver constraints unsat when verifying sum of lengths goal.")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message=error_msg,
                                details=f"Goal: LengthOfLine({line1}) + LengthOfLine({line2}) = {expected_answer}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"{line1}_{line2}_sum", sum_report)
                                return False, sum_report




                # Add this to the section handling goals in parse_and_verify_proof
                # --- Check for a cosine goal of the form:
                #     Value(Cos(MeasureOfAngle(CBA)))
                # Add this to the section handling goals in parse_and_verify_proof
                # --- Check for a cosine goal of the form:
                #     Value(Cos(MeasureOfAngle(CBA)))
                # --- Check for a cosine goal of the form: Value(Cos(MeasureOfAngle(XXX)))
                # --- Check for a cosine goal: Value(Cos(MeasureOfAngle(XXX)))
                # --- Check for a cosine goal of the form: Value(Cos(MeasureOfAngle(XXX)))
                # --- Check for a cosine goal of the form: Value(Cos(MeasureOfAngle(XXX)))
                cos_match = re.search(r'Value\(Cos\(MeasureOfAngle\((\w+)\)\)\)', goal_line)
                if cos_match:
                    angle_token = cos_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected = parse_special_answer(sections['ANSWER'][0].strip())

                        print(f"\nGoal cosine: Cos(MeasureOfAngle({angle_token}))")
                        print(f"Expected value: {expected}")

                        # Check if solver is satisfiable first
                        if self.solver.check() == sat:
                            model = self.solver.model()

                            # Get the cosine variable directly if it exists
                            cos_var_name = f"cos_{angle_token}"
                            if cos_var_name in self.variables:
                                cos_var = self.variables[cos_var_name]

                                # JUST CHECK the current value without adding any new constraints
                                try:
                                    current_cos = float(model.eval(cos_var).as_decimal(16).rstrip('?'))
                                    print(f"Current value for cos({angle_token}): {current_cos}")

                                    # Use a generous epsilon for comparison
                                    epsilon = 1e-5  # Very generous epsilon
                                    if abs(current_cos - expected) < epsilon:
                                        print(
                                            f"Success: cos({angle_token}) = {current_cos} ≈ {expected} (within tolerance)")
                                        return True, ""
                                    else:
                                        # Generate detailed report if values don't match
                                        error_msg = f"Failed to prove cosine goal: calculated value {current_cos} doesn't match expected {expected}."
                                        cos_report = self.generate_cosine_analysis_report(angle_token, expected,
                                                                                          current_cos, "incompatible")
                                        self.write_failure_report(f"cos_{angle_token}", cos_report)
                                        return False, error_msg
                                except Exception as e:
                                    print(f"Error evaluating cosine: {e}")

                            # Try to verify from the angle if no cosine variable exists
                            angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])

                            try:
                                current_angle = float(model.eval(angle_var).as_decimal(10).rstrip('?'))
                                import math
                                current_cos = math.cos(math.radians(current_angle))
                                print(f"Derived cos({angle_token}) = {current_cos} from angle = {current_angle}°")

                                epsilon = 1e-5
                                if abs(current_cos - expected) < epsilon:
                                    print(
                                        f"Success: cos({angle_token}) = {current_cos} ≈ {expected} (within tolerance)")
                                    return True, ""
                                else:
                                    # Generate report for failure
                                    error_msg = f"Failed to prove cosine goal: derived value {current_cos} doesn't match expected {expected}."
                                    cos_report = self.generate_cosine_analysis_report(angle_token, expected,
                                                                                      current_cos, "incompatible")
                                    self.write_failure_report(f"cos_{angle_token}", cos_report)
                                    return False, error_msg
                            except Exception as e:
                                print(f"Error calculating cosine from angle: {e}")

                            # If we reached here, we couldn't verify the cosine value
                            error_msg = "Failed to prove cosine goal: couldn't extract or verify cosine value."
                            cos_report = self.generate_cosine_analysis_report(angle_token, expected, None,
                                                                              "multiple_values")
                            self.write_failure_report(f"cos_{angle_token}", cos_report)
                            return False, error_msg
                        else:
                            error_msg = f"Failed to prove cosine goal: solver is unsatisfiable."
                            cos_report = self.generate_cosine_analysis_report(angle_token, expected, None,
                                                                              "unsatisfiable")
                            self.write_failure_report(f"cos_{angle_token}", cos_report)
                            return False, error_msg

                # --- Check for a sine goal of the form:
                #     Value(Sin(MeasureOfAngle(BAC)))
                # --- Check for a sine goal of the form:
                #     Value(Sin(MeasureOfAngle(BAC)))
                # --- Check for a sine goal of the form: Value(Sin(MeasureOfAngle(BAC)))
                # --- Check for a sine goal of the form: Value(Sin(MeasureOfAngle(BAC)))
                # --- Check for a sine goal of the form: Value(Sin(MeasureOfAngle(BAC)))
                # --- Check for a sine goal of the form: Value(Sin(MeasureOfAngle(BAC)))
                sin_match = re.search(r'Value\(Sin\(MeasureOfAngle\((\w+)\)\)\)', goal_line)
                if sin_match:
                    angle_token = sin_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected = parse_special_answer(sections['ANSWER'][0].strip())

                        print(f"\nGoal sine: Sin(MeasureOfAngle({angle_token}))")
                        print(f"Expected value: {expected}")

                        # Create a clean solver to work with
                        epsilon = 1e-8

                        if self.solver.check() == sat:
                            # Get the angle variable
                            angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])

                            # Check sine variable if it exists
                            sin_var_name = f"sin_{angle_token}"
                            sin_var = None
                            if sin_var_name in self.variables:
                                sin_var = self.variables[sin_var_name]
                                print(f"Found existing sine variable: {sin_var_name}")

                            # First check if the constraints are compatible with expected sine value
                            temp_solver1 = Solver()
                            for c in self.solver.assertions():
                                temp_solver1.add(c)

                            # Method 1: If we have a sine variable, check directly
                            if sin_var is not None:
                                temp_solver1.add(And(sin_var >= expected - epsilon, sin_var <= expected + epsilon))
                            else:
                                # Method 2: Otherwise, use possible angles that give this sine value
                                import math
                                # For sine in [-1, 1], we have two possible angles in [0, 360)
                                angle1 = math.degrees(math.asin(expected))  # First quadrant or fourth quadrant
                                angle2 = 180 - angle1  # Second quadrant or third quadrant

                                # Add constraint to check if either angle is possible
                                temp_solver1.add(Or(
                                    And(angle_var >= angle1 - epsilon, angle_var <= angle1 + epsilon),
                                    And(angle_var >= angle2 - epsilon, angle_var <= angle2 + epsilon)
                                ))

                            # Check if the expected sine value is compatible with the constraints
                            if temp_solver1.check() != sat:
                                error_msg = f"Failed to prove sine goal: constraints don't allow the expected value."

                                # Generate detailed report
                                sin_report = self.generate_sine_analysis_report(angle_token, expected, None,
                                                                                "incompatible")

                                print(f"Error: Constraints don't allow sin({angle_token}) = {expected}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal was: Sin(MeasureOfAngle({angle_token})) = {expected}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"sin_{angle_token}", sin_report)
                                return False, error_msg

                            # Now check if this is uniquely determined
                            model = self.solver.model()

                            # If we have a sine variable, check its uniqueness
                            if sin_var is not None:
                                sin_val = float(model.eval(sin_var).as_decimal(10).rstrip('?'))

                                # Check if sine value is uniquely determined
                                temp_solver2 = Solver()
                                for c in self.solver.assertions():
                                    temp_solver2.add(c)

                                temp_solver2.add(Or(sin_var < expected - epsilon, sin_var > expected + epsilon))

                                if temp_solver2.check() == sat:
                                    alt_model = temp_solver2.model()
                                    alt_sin = float(alt_model.eval(sin_var).as_decimal(10).rstrip('?'))

                                    error_msg = f"Failed to prove sine goal: sine value not uniquely determined."

                                    # Generate detailed report
                                    sin_report = self.generate_sine_analysis_report(angle_token, expected, alt_sin,
                                                                                    "multiple_values")

                                    print(f"Error: sin({angle_token}) could be {sin_val} or {alt_sin}")

                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message=error_msg,
                                        details=f"Goal was: Sin(MeasureOfAngle({angle_token})) = {expected}, but could also be {alt_sin}"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")
                                    if error.details:
                                        print("Details:", error.details)

                                    # Write report to file
                                    self.write_failure_report(f"sin_{angle_token}", sin_report)
                                    return False, sin_report
                            else:
                                # Check if the angle is uniquely determined
                                current_angle = float(model.eval(angle_var).as_decimal(10).rstrip('?'))

                                # Import math at the beginning of this block
                                import math

                                # Check which solution we're close to
                                angle1 = math.degrees(math.asin(expected))
                                angle2 = 180 - angle1

                                # Create a solver to check for different angles that would give different sine values
                                temp_solver2 = Solver()
                                for c in self.solver.assertions():
                                    temp_solver2.add(c)

                                # Try to find an angle that's significantly different and gives a different sine
                                if abs(current_angle - angle1) < 1:
                                    # Current angle is close to angle1, look for something different
                                    # but not just the other solution (angle2)
                                    temp_solver2.add(And(
                                        Or(angle_var < angle1 - 10, angle_var > angle1 + 10),
                                        Or(angle_var < angle2 - 10, angle_var > angle2 + 10)
                                    ))
                                elif abs(current_angle - angle2) < 1:
                                    # Current angle is close to angle2, look for something different
                                    # but not just the other solution (angle1)
                                    temp_solver2.add(And(
                                        Or(angle_var < angle1 - 10, angle_var > angle1 + 10),
                                        Or(angle_var < angle2 - 10, angle_var > angle2 + 10)
                                    ))
                                else:
                                    # Current angle is not close to either solution - try to find
                                    # a significantly different angle
                                    temp_solver2.add(Or(
                                        angle_var < current_angle - 10,
                                        angle_var > current_angle + 10
                                    ))

                                if temp_solver2.check() == sat:
                                    alt_model = temp_solver2.model()
                                    alt_angle = float(alt_model.eval(angle_var).as_decimal(10).rstrip('?'))
                                    alt_sin = math.sin(math.radians(alt_angle))

                                    # Only report error if the sine is actually different
                                    if abs(alt_sin - expected) >= epsilon:
                                        error_msg = f"Failed to prove sine goal: angle not uniquely determined."

                                        # Generate detailed report
                                        sin_report = self.generate_sine_analysis_report(angle_token, expected, alt_sin,
                                                                                        "multiple_values")

                                        print(f"Error: Angle {angle_token} could be {current_angle}° or {alt_angle}°")
                                        print(
                                            f"Giving sine values {math.sin(math.radians(current_angle))} and {alt_sin}")

                                        error = GeometricError(
                                            tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                            message=error_msg,
                                            details=f"Goal was: Sin(MeasureOfAngle({angle_token})) = {expected}"
                                        )
                                        print(f"\nError in {error.tier.name}: {error.message}")
                                        if error.details:
                                            print("Details:", error.details)

                                        # Write report to file
                                        self.write_failure_report(f"sin_{angle_token}", sin_report)
                                        return False, sin_report

                            # Success! The constraints uniquely determine the sine to be our expected value
                            print(f"Success: sin({angle_token}) = {expected} is verified.")
                            return True, ""
                        else:
                            error_msg = f"Failed to prove sine goal: solver is unsatisfiable."

                            # Generate detailed report for unsatisfiable case
                            sin_report = self.generate_sine_analysis_report(angle_token, expected, None,
                                                                            "unsatisfiable")

                            print("Solver constraints unsatisfiable when verifying sine goal.")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message=error_msg,
                                details=f"Goal was: Sin(MeasureOfAngle({angle_token})) = {expected}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)

                            # Write report to file
                            self.write_failure_report(f"sin_{angle_token}", sin_report)
                            return False, sin_report


                # 2. Quadrilateral area match section
                # 2. Quadrilateral area match section
                quad_area_match = re.search(r'Value\(AreaOfQuadrilateral\((\w+)\)\)', goal_line)
                if quad_area_match:
                    quad_name = quad_area_match.group(1)
                    print(f"\nDetected quadrilateral area goal: AreaOfQuadrilateral({quad_name})")  # Debug print

                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected = parse_special_answer(sections['ANSWER'][0].strip())

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
                                error_msg = "Failed to prove quadrilateral area goal: constraints don't allow the expected value."

                                # Generate detailed report for this case
                                quad_report = self.generate_quadrilateral_area_analysis_report(quad_name, expected,
                                                                                               None, "incompatible")

                                print(f"Error: Constraints don't allow the expected area {expected}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal was: AreaOfQuadrilateral({quad_name}) = {expected}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"area_{quad_name}", quad_report)
                                return False, quad_report

                            # Now check if any other value is allowed
                            temp_solver2 = Solver()
                            for c in self.solver.assertions():
                                temp_solver2.add(c)

                            # Add constraint: area != expected (outside epsilon range)
                            temp_solver2.add(Or(quad_area_var < expected - epsilon, quad_area_var > expected + epsilon))

                            if temp_solver2.check() == sat:
                                alt_model = temp_solver2.model()
                                alt_value = float(alt_model.eval(quad_area_var).as_decimal(10).rstrip('?'))

                                error_msg = "Failed to prove quadrilateral area goal: constraints allow multiple values."

                                # Generate detailed report for this case
                                quad_report = self.generate_quadrilateral_area_analysis_report(quad_name, expected,
                                                                                               alt_value,
                                                                                               "multiple_values")

                                print(f"Error: The proof doesn't uniquely determine area of {quad_name}.")
                                print(f"It could be {expected} but also {alt_value}")

                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal was: AreaOfQuadrilateral({quad_name}) = {expected}, but could also be {alt_value}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"area_{quad_name}", quad_report)
                                return False, quad_report

                            # Get the computed value from the model
                            model = self.solver.model()
                            calc_expr = model.eval(quad_area_var)
                            val_str = calc_expr.as_decimal(10)
                            if val_str.endswith('?'):
                                val_str = val_str[:-1]
                            calculated_value = float(val_str)

                            print(f"Calculated area for {quad_name} is {calculated_value}")
                            print(f"Success: The quadrilateral area is uniquely determined to be {expected}.")
                            return True, ""
                        else:
                            error_msg = "Failed to prove quadrilateral area goal: solver is unsatisfiable."

                            # Generate detailed report for unsatisfiable case
                            quad_report = self.generate_quadrilateral_area_analysis_report(quad_name, expected, None,
                                                                                           "unsatisfiable")

                            print("Solver constraints unsat when verifying quadrilateral area goal.")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message=error_msg,
                                details=f"Goal: AreaOfQuadrilateral({quad_name}) = {expected}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)

                            # Write report to file
                            self.write_failure_report(f"area_{quad_name}", quad_report)
                            return False, quad_report
                # --- Check for a division-of-lengths goal of the form:
                #     Value(Div(LengthOfLine(AF),LengthOfLine(AC)))
                # 3. Length division match section
                # --- Check for a division-of-lengths goal of the form:
                #     Value(Div(LengthOfLine(AF),LengthOfLine(AC)))
                length_div_match = re.search(r'Value\(Div\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)', goal_line)
                if length_div_match:
                    line1 = length_div_match.group(1)  # Numerator line (e.g., "AF")
                    line2 = length_div_match.group(2)  # Denominator line (e.g., "AC")

                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected_value = parse_special_answer(sections['ANSWER'][0].strip())

                        print(f"\nGoal division of lengths: Div(LengthOfLine({line1}),LengthOfLine({line2}))")
                        print(f"Expected value: {expected_value}")

                        # Get the length variables for both lines
                        len1 = self.add_length(line1[0], line1[1])
                        len2 = self.add_length(line2[0], line2[1])

                        if self.solver.check() == sat:
                            # First check if the solver allows a model that gives our expected ratio
                            temp_solver1 = Solver()
                            for c in self.solver.assertions():
                                temp_solver1.add(c)

                            # Add constraint: len1/len2 = expected_value
                            # This is equivalent to: len1 = expected_value * len2
                            epsilon = 1e-8
                            temp_solver1.add(And(
                                len2 > epsilon,  # Avoid division by zero
                                And(
                                    len1 >= (expected_value - epsilon) * len2,
                                    len1 <= (expected_value + epsilon) * len2
                                )
                            ))

                            if temp_solver1.check() != sat:
                                error_msg = "Failed to prove length division goal: constraints don't allow the expected value."

                                # Generate detailed report for this case
                                div_report = self.generate_division_analysis_report(line1, line2, expected_value, None,
                                                                                    "incompatible")

                                print(f"Error: Constraints don't allow {line1}/{line2} = {expected_value}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal was: Div(LengthOfLine({line1}),LengthOfLine({line2})) = {expected_value}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"{line1}_{line2}_div", div_report)
                                return False, div_report

                            # Now check if this ratio is uniquely determined
                            # Get the current model to see what values we have
                            model = self.solver.model()
                            try:
                                val1 = float(model.eval(len1).as_decimal(10).rstrip('?'))
                                val2 = float(model.eval(len2).as_decimal(10).rstrip('?'))

                                # Check for division by zero
                                if abs(val2) < epsilon:
                                    error_msg = "Division by zero in length ratio"

                                    # Generate detailed report for this case
                                    div_report = self.generate_division_analysis_report(line1, line2, expected_value,
                                                                                        None, "incompatible")
                                    div_report += "\nERROR: Division by zero detected. Line " + line2 + " has length approximately 0.\n"

                                    print("Error: Division by zero in length ratio")
                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message=error_msg,
                                        details=f"Line {line2} has length approximately 0"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")
                                    if error.details:
                                        print("Details:", error.details)

                                    # Write report to file
                                    self.write_failure_report(f"{line1}_{line2}_div", div_report)
                                    return False, div_report

                                computed_value = val1 / val2
                                print(f"Computed division: {computed_value}")

                                # Now check if there's a different valid ratio possible
                                temp_solver2 = Solver()
                                for c in self.solver.assertions():
                                    temp_solver2.add(c)

                                # We want to check if len1/len2 can have a different value
                                # This is equivalent to len1 != expected_value * len2
                                temp_solver2.add(
                                    Or(
                                        len1 < (expected_value - epsilon) * len2,
                                        len1 > (expected_value + epsilon) * len2
                                    )
                                )

                                if temp_solver2.check() == sat:
                                    alt_model = temp_solver2.model()
                                    alt_val1 = float(alt_model.eval(len1).as_decimal(10).rstrip('?'))
                                    alt_val2 = float(alt_model.eval(len2).as_decimal(10).rstrip('?'))

                                    # Check for division by zero in the alternative solution
                                    if abs(alt_val2) < epsilon:
                                        # Skip this alternative since it involves division by zero
                                        print("Note: Found an alternative solution but it involves division by zero")
                                    else:
                                        alt_ratio = alt_val1 / alt_val2

                                        error_msg = "Failed to prove length division goal: constraints allow multiple values."

                                        # Generate detailed report for this case
                                        div_report = self.generate_division_analysis_report(line1, line2,
                                                                                            expected_value, alt_ratio,
                                                                                            "multiple_values")

                                        print(f"Error: The proof doesn't uniquely determine the ratio {line1}/{line2}.")
                                        print(f"It could be {computed_value} but also {alt_ratio}")

                                        error = GeometricError(
                                            tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                            message=error_msg,
                                            details=f"Goal was: Div(LengthOfLine({line1}),LengthOfLine({line2})) = {expected_value}, but could also be {alt_ratio}"
                                        )
                                        print(f"\nError in {error.tier.name}: {error.message}")
                                        if error.details:
                                            print("Details:", error.details)

                                        # Write report to file
                                        self.write_failure_report(f"{line1}_{line2}_div", div_report)
                                        return False, div_report

                                # Check if computed value matches expected value
                                if abs(computed_value - expected_value) >= epsilon:
                                    error_msg = f"Failed to prove length division goal: computed value {computed_value} doesn't match expected {expected_value}."

                                    # Generate detailed report for this case
                                    div_report = self.generate_division_analysis_report(line1, line2, expected_value,
                                                                                        computed_value, "incompatible")

                                    print(f"Error: Computed division {computed_value} != expected {expected_value}")
                                    error = GeometricError(
                                        tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                        message=error_msg,
                                        details=f"Goal was: Div(LengthOfLine({line1}),LengthOfLine({line2})) = {expected_value}, computed: {computed_value}"
                                    )
                                    print(f"\nError in {error.tier.name}: {error.message}")
                                    if error.details:
                                        print("Details:", error.details)

                                    # Write report to file
                                    self.write_failure_report(f"{line1}_{line2}_div", div_report)
                                    return False, div_report

                                print(
                                    f"Success: The length ratio {line1}/{line2} is uniquely determined to be {expected_value}.")
                                return True, ""

                            except Exception as e:
                                error_msg = f"Error converting length values: {str(e)}"

                                # Generate detailed report for this case
                                div_report = self.generate_division_analysis_report(line1, line2, expected_value, None,
                                                                                    "incompatible")
                                div_report += f"\nERROR: {str(e)}\n"

                                print("Error converting length values:", e)
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=str(e)
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"{line1}_{line2}_div", div_report)
                                return False, div_report
                        else:
                            error_msg = "Failed to prove length division goal: solver is unsatisfiable."

                            # Generate detailed report for unsatisfiable case
                            div_report = self.generate_division_analysis_report(line1, line2, expected_value, None,
                                                                                "unsatisfiable")

                            print("Solver constraints unsat when evaluating division-of-lengths goal.")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message=error_msg,
                                details=f"Goal was: Div(LengthOfLine({line1}),LengthOfLine({line2})) = {expected_value}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)

                            # Write report to file
                            self.write_failure_report(f"{line1}_{line2}_div", div_report)
                            return False, div_report

                # --- Check for a perimeter goal of the form:
                #     Value(PerimeterOfTriangle(ABC))
                # 4. Perimeter match section
                # --- Check for a perimeter goal of the form:
                #     Value(PerimeterOfTriangle(ABC))
                perimeter_match = re.search(r'Value\(PerimeterOfTriangle\((\w+)\)\)', goal_line)
                if perimeter_match:
                    triangle = perimeter_match.group(1)
                    print(f"\nDetected perimeter goal: PerimeterOfTriangle({triangle})")  # Debug print

                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected_answer = parse_special_answer(sections['ANSWER'][0].strip())
                        print(f"\nGoal triangle perimeter: {triangle}")
                        print(f"Expected answer: {expected_answer}")

                        # Create detailed report
                        perimeter_report = self.generate_perimeter_analysis_report(triangle, expected_answer)

                        if triangle in self.triangle_perimeters:
                            perimeter_var = self.triangle_perimeters[triangle]
                        else:
                            perimeter_var = self.calculate_perimeter(triangle)
                            self.triangle_perimeters[triangle] = perimeter_var

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
                                error_msg = "Failed to prove triangle perimeter goal: constraints don't allow the expected value."

                                # Generate detailed report for this case
                                perimeter_report = self.generate_perimeter_analysis_report(triangle, expected_answer,
                                                                                           None, "incompatible")

                                print(f"Error: Constraints don't allow the expected perimeter {expected_answer}")
                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal was: PerimeterOfTriangle({triangle}) = {expected_answer}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"perimeter_{triangle}", perimeter_report)
                                return False, perimeter_report

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

                                error_msg = "Failed to prove triangle perimeter goal: constraints allow multiple values."

                                # Generate detailed report for this case
                                perimeter_report = self.generate_perimeter_analysis_report(triangle, expected_answer,
                                                                                           alt_value, "multiple_values")

                                print(f"Error: The proof doesn't uniquely determine perimeter of {triangle}.")
                                print(f"It could be {expected_answer} but also {alt_value}")

                                error = GeometricError(
                                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                    message=error_msg,
                                    details=f"Goal was: PerimeterOfTriangle({triangle}) = {expected_answer}, but could also be {alt_value}"
                                )
                                print(f"\nError in {error.tier.name}: {error.message}")
                                if error.details:
                                    print("Details:", error.details)

                                # Write report to file
                                self.write_failure_report(f"perimeter_{triangle}", perimeter_report)
                                return False, perimeter_report

                            # Get the computed value from the model
                            model = self.solver.model()
                            calculated_value_str = model.eval(perimeter_var).as_decimal(10)
                            if calculated_value_str.endswith('?'):
                                calculated_value_str = calculated_value_str[:-1]

                            try:
                                calculated_float = float(Fraction(calculated_value_str))
                            except Exception as e:
                                error_msg = f"Could not convert the calculated perimeter to a float: {str(e)}"
                                perimeter_report += f"Error: Could not convert the calculated perimeter: {str(e)}\n"
                                print("Could not convert the calculated perimeter to a float:", e)

                                # Write report to file
                                self.write_failure_report(f"perimeter_{triangle}", perimeter_report)
                                return False, perimeter_report

                            print(f"Calculated perimeter for {triangle} is {calculated_float}")
                            print(f"Success: The triangle perimeter is uniquely determined to be {expected_answer}.")
                            return True, ""
                        else:
                            error_msg = "Failed to prove perimeter goal: solver is unsatisfiable."

                            # Generate detailed report for unsatisfiable case
                            perimeter_report = self.generate_perimeter_analysis_report(triangle, expected_answer, None,
                                                                                       "unsatisfiable")

                            print("Error: Constraints are unsat (solver.check() == unsat).")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message=error_msg,
                                details=f"Goal: PerimeterOfTriangle({triangle}) = {expected_answer}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)

                            # Write report to file
                            self.write_failure_report(f"perimeter_{triangle}", perimeter_report)
                            return False, perimeter_report

                # --- Check for a length goal of the form:
                #     Value(LengthOfLine(AB))
                length_match = re.search(r'Value\(LengthOfLine\((\w+)\)\)', goal_line)
                if length_match:
                    line_name = length_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected_answer = parse_special_answer(sections['ANSWER'][0].strip())
                        print(f"\nGoal line: {line_name}")
                        print(f"Expected answer: {expected_answer}")
                        success, error_msg = self.verify_goal_length(line_name[0], line_name[1], expected_answer)
                        if not success:
                            return False, error_msg
                        else:
                            return True, ""

                # --- Check for an angle goal of the form:
                #     Value(MeasureOfAngle(ABC))
                angle_match = re.search(r'Value\(MeasureOfAngle\((\w+)\)\)', goal_line)
                if angle_match:
                    goal_angle = angle_match.group(1)
                    if 'ANSWER' in sections and sections['ANSWER']:
                        expected_answer = parse_special_answer(sections['ANSWER'][0].strip())
                        print(f"\nGoal angle: {goal_angle}")
                        print(f"Expected answer: {expected_answer}")

                        # Use the updated verify_algebraic_goal that returns a tuple
                        success, goal_feedback = self.verify_algebraic_goal(goal_angle, expected_answer)

                        if success:
                            return True, ""
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
                            return False, goal_feedback

                # --- Check for a general goal expression of the form: Value(<expression>)
                # Complete implementation for the general goal match section
                # The complete updated general_match handler
                general_match = re.search(r'Value\((.+)\)', goal_line)
                if general_match:
                    goal_expr = general_match.group(1).strip()

                    # Create a report
                    general_report = f"Analysis for general goal expression: {goal_expr}\n"

                    if self.solver.check() == sat:
                        model = self.solver.model()
                        answer_str = sections['ANSWER'][0].strip() if (
                                'ANSWER' in sections and sections['ANSWER']) else None
                        if answer_str is None:
                            error_msg = "No answer provided in ANSWER section."
                            general_report += "No answer provided in ANSWER section.\n"
                            print("No answer provided in ANSWER section.")

                            # Write report to file
                            self.write_failure_report(f"general_expr", general_report)
                            return False, general_report

                        # Add expected value to report
                        try:
                            expected_value = parse_special_answer(answer_str)
                            general_report += f"Expected value: {expected_value}\n\n"
                        except Exception as e:
                            error_msg = f"Error parsing answer '{answer_str}': {str(e)}"
                            general_report += f"Error parsing answer '{answer_str}': {str(e)}\n"
                            print(f"Error parsing answer '{answer_str}': {e}")

                            # Write report to file
                            self.write_failure_report(f"general_expr", general_report)
                            return False, general_report

                        # Special handling if goal_expr is of the form Sub(...)
                        if goal_expr.startswith("Sub(") and goal_expr.endswith(")"):
                            inner = goal_expr[4:-1]
                            parts = inner.split(',')
                            if len(parts) == 2:
                                expr1_str = parts[0].strip()
                                expr2_str = parts[1].strip()

                                # Handle angle measure subtraction
                                angle1_match = re.match(r'MeasureOfAngle\((\w+)\)', expr1_str)
                                angle2_match = re.match(r'MeasureOfAngle\((\w+)\)', expr2_str)
                                if angle1_match and angle2_match:
                                    angle1_name = angle1_match.group(1)
                                    angle2_name = angle2_match.group(1)

                                    # Get angle variables
                                    angle1_var = self.add_angle(angle1_name[0], angle1_name[1], angle1_name[2])
                                    angle2_var = self.add_angle(angle2_name[0], angle2_name[1], angle2_name[2])

                                    # Evaluate each angle
                                    angle1_val = float(model.eval(angle1_var).as_decimal(10).rstrip('?'))
                                    angle2_val = float(model.eval(angle2_var).as_decimal(10).rstrip('?'))

                                    # Calculate difference
                                    computed_value = angle1_val - angle2_val
                                    general_report += f"First angle {angle1_name}: {angle1_val}\n"
                                    general_report += f"Second angle {angle2_name}: {angle2_val}\n"
                                    general_report += f"Computed difference: {computed_value}\n"

                                    epsilon = 1e-8
                                    if abs(computed_value - expected_value) >= epsilon:
                                        error_msg = "Failed to prove angle subtraction goal."
                                        general_report += f"Error: Computed value {computed_value} != expected {expected_value}\n"

                                        print(f"Error: Computed value {computed_value} != expected {expected_value}")
                                        error = GeometricError(
                                            tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                            message=error_msg,
                                            details=f"Computed: {computed_value}, expected: {expected_value}"
                                        )
                                        print(f"\nError in {error.tier.name}: {error.message}")
                                        if error.details:
                                            print("Details:", error.details)

                                        # Write report to file
                                        self.write_failure_report(f"sub_angles_{angle1_name}_{angle2_name}",
                                                                  general_report)
                                        return False, general_report

                                    # Check uniqueness - can angle difference be something other than expected_value?
                                    temp_solver = Solver()
                                    for c in self.solver.assertions():
                                        temp_solver.add(c)

                                    # Add constraint that difference must be outside epsilon range of expected
                                    temp_solver.add(
                                        Or(
                                            angle1_var - angle2_var < expected_value - epsilon,
                                            angle1_var - angle2_var > expected_value + epsilon
                                        )
                                    )

                                    if temp_solver.check() == sat:
                                        alt_model = temp_solver.model()
                                        alt_angle1 = float(alt_model.eval(angle1_var).as_decimal(10).rstrip('?'))
                                        alt_angle2 = float(alt_model.eval(angle2_var).as_decimal(10).rstrip('?'))
                                        alt_value = alt_angle1 - alt_angle2

                                        error_msg = "Failed to prove angle subtraction goal: constraints allow multiple values."
                                        general_report += f"Error: The proof doesn't uniquely determine the angle difference.\n"
                                        general_report += f"It could be {computed_value} but also {alt_value}\n"
                                        general_report += f"Alternative values: {angle1_name}={alt_angle1}, {angle2_name}={alt_angle2}\n"

                                        print(f"Error: The proof doesn't uniquely determine the angle difference.")
                                        print(f"It could be {computed_value} but also {alt_value}")

                                        error = GeometricError(
                                            tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                            message=error_msg,
                                            details=f"Goal was: {goal_expr} = {expected_value}, but could also be {alt_value}"
                                        )
                                        print(f"\nError in {error.tier.name}: {error.message}")
                                        if error.details:
                                            print("Details:", error.details)

                                        # Write report to file
                                        self.write_failure_report(f"sub_angles_{angle1_name}_{angle2_name}",
                                                                  general_report)
                                        return False, general_report

                                    print(
                                        f"Success: Angle difference {angle1_name} - {angle2_name} = {expected_value} is verified.")
                                    return True, ""

                                # Handle area subtraction (existing code)
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
                                            error_msg = f"Error converting area values: {str(e)}"
                                            general_report += f"Error converting area values: {str(e)}\n"
                                            print("Error converting area values:", e)

                                            # Write report to file
                                            self.write_failure_report(f"sub_expr_{circle}_{tri}", general_report)
                                            return False, general_report

                                        computed_value = area_circle_val - area_triangle_val
                                        general_report += f"Computed value: {computed_value}\n"

                                        epsilon = 1e-8
                                        if abs(computed_value - expected_value) >= epsilon:
                                            error_msg = "Failed to prove goal (Sub form)."
                                            general_report += f"Error: Computed value {computed_value} != expected {expected_value}\n"

                                            print(
                                                f"Error: Computed value {computed_value} != expected {expected_value}")
                                            error = GeometricError(
                                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                                message=error_msg,
                                                details=f"Computed: {computed_value}, expected: {expected_value}"
                                            )
                                            print(f"\nError in {error.tier.name}: {error.message}")
                                            if error.details:
                                                print("Details:", error.details)

                                            # Write report to file
                                            self.write_failure_report(f"sub_expr_{circle}_{tri}", general_report)
                                            return False, general_report

                                        # Check uniqueness - can area difference be something other than expected_value?
                                        temp_solver = Solver()
                                        for c in self.solver.assertions():
                                            temp_solver.add(c)

                                        # Add constraint that sub-expression result must be outside epsilon range of expected
                                        temp_solver.add(
                                            Or(
                                                circle_area_var - triangle_area_var < expected_value - epsilon,
                                                circle_area_var - triangle_area_var > expected_value + epsilon
                                            )
                                        )

                                        if temp_solver.check() == sat:
                                            alt_model = temp_solver.model()
                                            alt_circle = float(
                                                alt_model.eval(circle_area_var).as_decimal(10).rstrip('?'))
                                            alt_triangle = float(
                                                alt_model.eval(triangle_area_var).as_decimal(10).rstrip('?'))
                                            alt_value = alt_circle - alt_triangle

                                            error_msg = "Failed to prove goal (Sub form): constraints allow multiple values."
                                            general_report += f"Error: The proof doesn't uniquely determine the difference between areas.\n"
                                            general_report += f"It could be {computed_value} but also {alt_value}\n"

                                            print(
                                                f"Error: The proof doesn't uniquely determine the difference between areas.")
                                            print(f"It could be {computed_value} but also {alt_value}")

                                            error = GeometricError(
                                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                                message=error_msg,
                                                details=f"Goal was: Sub({expr1_str},{expr2_str}) = {expected_value}, but could also be {alt_value}"
                                            )
                                            print(f"\nError in {error.tier.name}: {error.message}")
                                            if error.details:
                                                print("Details:", error.details)

                                            # Write report to file
                                            self.write_failure_report(f"sub_expr_{circle}_{tri}", general_report)
                                            return False, general_report

                                        print(
                                            "Success: Goal expression (Sub form) matches expected value and is uniquely determined.")
                                        return True, ""

                        # For general expressions, build a mapping for evaluation
                        mapping = {}
                        for var, z3var in self.variables.items():
                            try:
                                val = model.eval(z3var, model_completion=True)
                                val_str = str(val).replace('?', '')
                                mapping[var] = float(Fraction(val_str))
                            except Exception as e:
                                error_msg = f"Error converting free variable {var}: {str(e)}"
                                general_report += f"Error converting free variable {var}: {str(e)}\n"
                                print(f"Error converting free variable {var}: {e}")

                                # Write report to file
                                self.write_failure_report(f"general_expr", general_report)
                                return False, general_report

                        # Also add circle areas and triangle areas if needed
                        for circle, var in self.circle_areas.items():
                            value = model.eval(var)
                            value_str = str(value).replace('?', '')
                            try:
                                mapping[f"ac_{circle.lower()}"] = float(Fraction(value_str))
                            except Exception as e:
                                error_msg = f"Error converting circle area for {circle}: {str(e)}"
                                general_report += f"Error converting circle area for {circle}: {str(e)}\n"
                                print("Error converting circle area for", circle, ":", e)

                                # Write report to file
                                self.write_failure_report(f"general_expr", general_report)
                                return False, general_report

                        for tri, var in self.triangle_areas.items():
                            value = model.eval(var)
                            value_str = str(value).replace('?', '')
                            try:
                                mapping[f"at_{tri.lower()}"] = float(Fraction(value_str))
                            except Exception as e:
                                error_msg = f"Error converting triangle area for {tri}: {str(e)}"
                                general_report += f"Error converting triangle area for {tri}: {str(e)}\n"
                                print("Error converting triangle area for", tri, ":", e)

                                # Write report to file
                                self.write_failure_report(f"general_expr", general_report)
                                return False, general_report

                        # Add additional symbols needed for evaluation
                        import math
                        mapping["pi"] = math.pi
                        mapping["sqrt"] = math.sqrt

                        # Define helper functions to support evaluation
                        def Sub(x, y):
                            return x - y

                        mapping["Sub"] = Sub

                        try:
                            computed_value = eval(goal_expr, mapping)
                            general_report += f"Computed value: {computed_value}\n"
                        except Exception as e:
                            error_msg = f"Error evaluating general goal expression: {str(e)}"
                            general_report += f"Error evaluating general goal expression: {str(e)}\n"

                            # Enhanced error reporting
                            general_report += "\nPossible causes of this error:\n"
                            general_report += "1. The expression contains functions or operations not defined in the evaluation context\n"
                            general_report += "2. Variables in the expression may not be properly defined or constrained\n"
                            general_report += "3. The proof may not have established all necessary relationships\n\n"

                            general_report += "Steps to debug:\n"
                            general_report += f"1. Check if all variables in '{goal_expr}' have been defined in your proof\n"
                            general_report += "2. Verify that your theorems correctly establish the necessary relationships\n"
                            general_report += "3. Review the TEXT_CDL section to ensure all required premises are included\n"

                            print(f"Error evaluating general goal expression: {e}")
                            # Write report to file
                            self.write_failure_report(f"general_expr", general_report)
                            return False, general_report

                        epsilon = 1e-8
                        if abs(computed_value - expected_value) >= epsilon:
                            error_msg = "Failed to prove general goal expression."
                            general_report += f"Error: Computed general goal value {computed_value} != expected {expected_value}\n"

                            print(f"Error: Computed general goal value {computed_value} != expected {expected_value}")
                            error = GeometricError(
                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                message=error_msg,
                                details=f"Computed: {computed_value}, expected: {expected_value}"
                            )
                            print(f"\nError in {error.tier.name}: {error.message}")
                            if error.details:
                                print("Details:", error.details)

                            # Write report to file
                            self.write_failure_report(f"general_expr", general_report)
                            return False, general_report

                        # For general expressions, uniqueness checking is complex
                        # We need to identify which variables influence the goal expression
                        # For simplicity, we'll check if any variable in the mapping can change
                        # while still satisfying all constraints

                        relevant_vars = []
                        for var_name, z3_var in self.variables.items():
                            if var_name in goal_expr:
                                relevant_vars.append((var_name, z3_var))

                        if relevant_vars:
                            general_report += f"Checking uniqueness for the general expression...\n"
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
                                        if abs(alt_value - expected_value) >= epsilon:
                                            error_msg = "Failed to prove general goal: constraints allow multiple values."
                                            general_report += f"Error: The proof doesn't uniquely determine the result of {goal_expr}.\n"
                                            general_report += f"It could be {computed_value} but could also be {alt_value}\n"

                                            print(
                                                f"Error: The proof doesn't uniquely determine the result of {goal_expr}.")
                                            print(f"It could be {computed_value} but could also be {alt_value}")

                                            error = GeometricError(
                                                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                                                message=error_msg,
                                                details=f"Goal was: {goal_expr} = {expected_value}, but could also evaluate to {alt_value}"
                                            )
                                            print(f"\nError in {error.tier.name}: {error.message}")
                                            if error.details:
                                                print("Details:", error.details)

                                            # Write report to file
                                            self.write_failure_report(f"general_expr", general_report)
                                            return False, general_report
                                    except Exception as e:
                                        print(f"Error evaluating alternative: {e}")
                                        general_report += f"Warning: Error evaluating alternative: {e}\n"
                                        # Continue with success if we can't evaluate the alternative

                        print(
                            "Success: General goal expression matches expected value and appears to be uniquely determined.")
                        return True, ""
                    else:
                        # Unsatisfiable case - create a detailed report
                        error_msg = "Failed to prove general goal: solver is unsatisfiable."

                        # Try to parse expected value from ANSWER section for the detailed report
                        expected_value = None
                        if 'ANSWER' in sections and sections['ANSWER']:
                            try:
                                expected_value = parse_special_answer(sections['ANSWER'][0].strip())
                            except Exception as e:
                                print(f"Error parsing answer: {e}")

                        # Special handling for Sub expressions in the unsatisfiable case
                        if goal_expr.startswith("Sub(") and goal_expr.endswith(")"):
                            inner = goal_expr[4:-1]
                            parts = inner.split(',')
                            if len(parts) == 2:
                                expr1_str = parts[0].strip()
                                expr2_str = parts[1].strip()
                                angle1_match = re.match(r'MeasureOfAngle\((\w+)\)', expr1_str)
                                angle2_match = re.match(r'MeasureOfAngle\((\w+)\)', expr2_str)

                                if angle1_match and angle2_match:
                                    # It's an angle subtraction
                                    angle1_name = angle1_match.group(1)
                                    angle2_name = angle2_match.group(1)

                                    # Create a more detailed report specifically for angle subtraction
                                    detailed_report = f"Analysis Report for {self.question_name}\n"
                                    detailed_report += "=" * 60 + "\n\n"
                                    detailed_report += f"Goal: {goal_expr}\n"
                                    detailed_report += f"Expected value: {expected_value}\n\n"
                                    detailed_report += f"This goal represents the difference between two angles:\n"
                                    detailed_report += f"- First angle: {expr1_str} ({angle1_name})\n"
                                    detailed_report += f"- Second angle: {expr2_str} ({angle2_name})\n\n"

                                    # Find theorems that constrain these angles
                                    angle1_theorems = []
                                    angle2_theorems = []
                                    for theorem_info in self.theorem_sequence:
                                        for conclusion in theorem_info["conclusions"]:
                                            if angle1_name in conclusion:
                                                angle1_theorems.append({
                                                    "step": theorem_info["step_number"],
                                                    "theorem": theorem_info["theorem_name"],
                                                    "args": theorem_info["args"],
                                                    "conclusion": conclusion
                                                })
                                            if angle2_name in conclusion:
                                                angle2_theorems.append({
                                                    "step": theorem_info["step_number"],
                                                    "theorem": theorem_info["theorem_name"],
                                                    "args": theorem_info["args"],
                                                    "conclusion": conclusion
                                                })

                                    if angle1_theorems:
                                        detailed_report += f"Theorems involving {angle1_name}:\n"
                                        detailed_report += "-" * 60 + "\n"
                                        for theorem in angle1_theorems:
                                            detailed_report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])})\n"
                                            detailed_report += f"  Conclusion: {theorem['conclusion']}\n\n"
                                    else:
                                        detailed_report += f"No theorems directly constrain angle {angle1_name}.\n\n"

                                    if angle2_theorems:
                                        detailed_report += f"Theorems involving {angle2_name}:\n"
                                        detailed_report += "-" * 60 + "\n"
                                        for theorem in angle2_theorems:
                                            detailed_report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])})\n"
                                            detailed_report += f"  Conclusion: {theorem['conclusion']}\n\n"
                                    else:
                                        detailed_report += f"No theorems directly constrain angle {angle2_name}.\n\n"

                                    # Add angle variables to check if they're defined
                                    try:
                                        self.add_angle(angle1_name[0], angle1_name[1], angle1_name[2])
                                        detailed_report += f"Angle {angle1_name} is defined in the system.\n"
                                    except Exception:
                                        detailed_report += f"ERROR: Angle {angle1_name} could not be defined in the system!\n"

                                    try:
                                        self.add_angle(angle2_name[0], angle2_name[1], angle2_name[2])
                                        detailed_report += f"Angle {angle2_name} is defined in the system.\n\n"
                                    except Exception:
                                        detailed_report += f"ERROR: Angle {angle2_name} could not be defined in the system!\n\n"

                                    # Diagnosis section
                                    detailed_report += "Diagnosis:\n"
                                    detailed_report += "-" * 60 + "\n"
                                    detailed_report += "The solver found the constraints to be contradictory. Your proof contains inconsistent\n"
                                    detailed_report += "constraints that cannot be satisfied simultaneously.\n\n"

                                    detailed_report += "For this angle subtraction goal, consider these possible causes:\n"
                                    detailed_report += "1. One or both angles may not be sufficiently constrained in your proof\n"
                                    detailed_report += "2. The theorems you've applied may lead to contradictory angle values\n"
                                    detailed_report += "3. Your proof may be missing steps that establish necessary angle relationships\n"
                                    detailed_report += "4. Check if all points in the angles are correctly defined in the construction\n\n"

                                    detailed_report += "Recommended steps:\n"
                                    detailed_report += f"1. Verify that angles {angle1_name} and {angle2_name} are properly constrained\n"
                                    detailed_report += "2. Check if you're missing theorems that establish the angle measures\n"
                                    detailed_report += "3. Review your proof sequence for consistency\n"

                                    # Write report to file and return
                                    self.write_failure_report(f"sub_angles_{angle1_name}_{angle2_name}",
                                                              detailed_report)
                                    return False, detailed_report

                        # Generate the general analysis report for other cases
                        detailed_report = self.generate_general_goal_analysis_report(goal_expr, expected_value)

                        print("Solver constraints unsat when evaluating general goal.")
                        error = GeometricError(
                            tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                            message=error_msg,
                            details=f"Goal: {goal_expr} = {expected_value if expected_value is not None else '?'}"
                        )
                        print(f"\nError in {error.tier.name}: {error.message}")
                        if error.details:
                            print("Details:", error.details)

                        # Write report to file
                        self.write_failure_report(f"general_expr_{goal_expr}", detailed_report)
                        return False, detailed_report

                feedback = "Error: Could not parse goal (not a recognized goal type)"
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
                return False, feedback


            return True, ""

        except Exception as e:

            print(f"Error during proof verification: {str(e)}")

            import traceback

            traceback.print_exc()

            return False, f"Error during proof verification: {str(e)}"

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

        # 11. Collect arcs involving ONLY goal points
        related_arcs = []
        for arc_name in self.arcs:
            # Extract arc points (typically in format "arc_ABC")
            arc_points = arc_name.split('_')[1] if '_' in arc_name else arc_name
            arc_points_set = set(arc_points)
            if arc_points_set.issubset(goal_points_set):
                related_arcs.append(f"Arc {arc_points}")
        related_facts["Arcs"] = related_arcs

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

    def generate_perimeter_analysis_report(self, triangle, expected_value, alt_value=None,
                                           solver_state="multiple_values"):
        """Generate a detailed report for triangle perimeter goals that couldn't be verified."""

        # Create the report content as a string
        report = f"Analysis Report for {self.question_name}\n"
        report += "=" * 60 + "\n\n"
        report += f"Goal: Perimeter of triangle {triangle}\n"
        report += f"Expected value: {expected_value}\n\n"

        # Extract points involved in the triangle
        tri_points = list(triangle)

        # Check if the triangle exists in our system
        normalized_triangle = self.normalize_triangle(triangle)
        if normalized_triangle in self.polygons:
            report += f"Triangle {triangle} is defined in the system.\n"
        else:
            report += f"Triangle {triangle} is not explicitly defined in the system.\n"
            report += "You need to establish this triangle through theorems.\n\n"

        # Check for triangle properties
        triangle_properties = []
        if triangle in self.right_triangles:
            triangle_properties.append("right triangle")
        if hasattr(self, 'isosceles_triangles') and triangle in self.isosceles_triangles:
            triangle_properties.append("isosceles triangle")
        if hasattr(self, 'equilateral_triangles') and triangle in self.equilateral_triangles:
            triangle_properties.append("equilateral triangle")
        if hasattr(self, 'similar_triangles'):
            similar_to = []
            for tri_pair in self.similar_triangles:
                if triangle in tri_pair:
                    other_tri = tri_pair[0] if tri_pair[1] == triangle else tri_pair[1]
                    similar_to.append(other_tri)
            if similar_to:
                triangle_properties.append(f"similar to triangle(s): {', '.join(similar_to)}")

        if triangle_properties:
            report += f"Triangle {triangle} is a {', '.join(triangle_properties)}.\n"

        # Get side lengths of the triangle
        report += "\nSide lengths of triangle:\n"
        sides_found = 0
        side_lengths = []

        for i in range(len(triangle)):
            p1 = triangle[i]
            p2 = triangle[(i + 1) % len(triangle)]
            side = p1 + p2
            normalized_side = self.normalize_line_name(side)
            length_var_name = f"length_{normalized_side}"

            if length_var_name in self.lengths:
                sides_found += 1
                if self.solver.check() == sat:
                    model = self.solver.model()
                    try:
                        length_val = float(model.eval(self.lengths[length_var_name]).as_decimal(10).rstrip('?'))
                        report += f"  Side {side}: {length_val}\n"
                        side_lengths.append(length_val)
                    except Exception as e:
                        report += f"  Side {side}: Error evaluating length - {str(e)}\n"
            else:
                report += f"  Side {side}: Not explicitly defined\n"

        # Calculate perimeter from side lengths if available
        if len(side_lengths) == 3:
            calculated_perimeter = sum(side_lengths)
            report += f"\nCalculated perimeter: {calculated_perimeter}\n"
            if abs(calculated_perimeter - expected_value) >= 1e-8:
                report += f"This doesn't match the expected value {expected_value}.\n"

        # Check if perimeter variable exists
        if triangle in self.triangle_perimeters:
            report += f"\nPerimeter variable for triangle {triangle} exists in the system.\n"

            if self.solver.check() == sat:
                model = self.solver.model()
                try:
                    perimeter_val = float(model.eval(self.triangle_perimeters[triangle]).as_decimal(10).rstrip('?'))
                    report += f"Current perimeter value: {perimeter_val}\n"

                    if abs(perimeter_val - expected_value) >= 1e-8:
                        report += f"This doesn't match the expected value {expected_value}.\n"
                except Exception as e:
                    report += f"Error evaluating perimeter: {str(e)}\n"
        else:
            report += f"\nNo perimeter variable for triangle {triangle} has been defined.\n"
            report += "You need to establish this through the triangle_perimeter_formula theorem.\n"

        # Find theorems relevant to this triangle's perimeter
        report += f"\nTheorems related to triangle {triangle} in your proof:\n"
        report += "-" * 60 + "\n"
        related_theorems = []

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if the triangle is mentioned in the conclusions
            for conclusion in theorem_info["conclusions"]:
                if f"PerimeterOfTriangle({triangle})" in conclusion or triangle in conclusion:
                    is_related = True
                    break

            # Check if mentioned in the premise
            if triangle in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(triangle in arg for arg in theorem_info["args"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        if related_theorems:
            for theorem in related_theorems:
                report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n"
                report += f"  Conclusion: {theorem['conclusion']}\n\n"
        else:
            report += f"No theorems directly involving triangle {triangle} were found in your proof.\n"
            report += "You may need to apply the triangle_perimeter_formula theorem to calculate the perimeter.\n\n"

        # Add solver constraints related to this goal
        report += "Solver constraints directly related to this goal:\n"
        report += "-" * 60 + "\n"

        perimeter_var_name = f"perimeter_{triangle}" if triangle in self.triangle_perimeters else None

        relevant_constraints = []
        for c in self.solver.assertions():
            c_str = str(c)
            if perimeter_var_name and perimeter_var_name in c_str:
                relevant_constraints.append(c_str)
            elif f"PerimeterOfTriangle({triangle})" in c_str or triangle in c_str:
                relevant_constraints.append(c_str)

        if relevant_constraints:
            for i, constraint in enumerate(relevant_constraints):
                report += f"{i + 1}. {constraint}\n"
            report += "\n"
        else:
            report += "No direct constraints found involving this triangle's perimeter.\n\n"

        # Add an explanation based on the solver state
        report += "Diagnosis:\n"
        report += "-" * 60 + "\n"

        if solver_state == "unsatisfiable":
            report += "The solver found the constraints to be contradictory. This means your proof contains\n"
            report += "inconsistent constraints that cannot be satisfied simultaneously.\n\n"
            report += "Possible causes:\n"
            report += "1. Incorrect triangle side lengths in premises\n"
            report += "2. Improper theorem application\n"
            report += "3. Conclusions that contradict earlier assertions\n"
            report += "4. Errors in the perimeter calculation\n\n"
        elif solver_state == "incompatible":
            report += f"The geometric constraints in your proof don't allow the perimeter of {triangle} to be {expected_value}.\n"
            report += "This means your proof implies a different perimeter than expected.\n\n"
            report += "Check that:\n"
            report += "1. Your side length values are correctly specified\n"
            report += "2. You've correctly identified the triangle in question\n"
            report += "3. All sides are included in the perimeter calculation\n"
        else:  # multiple_values
            report += f"Your proof doesn't uniquely determine the perimeter of triangle {triangle}.\n"
            report += "Multiple solutions are possible with the current constraints.\n"
            if alt_value is not None:
                report += f"It could be {expected_value} but also {alt_value}\n\n"
            report += "You need to add more constraints by applying additional theorems.\n"
            report += "Focus on fixing the lengths of each side of the triangle.\n"

        return report
    def generate_quadrilateral_area_analysis_report(self, quad_name, expected_value, alt_value=None,
                                                    solver_state="multiple_values"):
        """Generate a detailed report for quadrilateral area goals that couldn't be verified."""

        # Create the report content as a string
        report = f"Analysis Report for {self.question_name}\n"
        report += "=" * 60 + "\n\n"
        report += f"Goal: Area of quadrilateral {quad_name}\n"
        report += f"Expected value: {expected_value}\n\n"

        # Extract points involved in the quadrilateral
        quad_points = list(quad_name)

        # Check if the quadrilateral is defined in our system
        if quad_name in self.polygons:
            report += f"Quadrilateral {quad_name} is defined in the system.\n"
        else:
            report += f"Quadrilateral {quad_name} is not explicitly defined in the system.\n"
            report += "You need to establish this quadrilateral through appropriate theorems.\n\n"

        # Check if the quadrilateral has a special type
        special_types = []
        if quad_name in self.parallelograms:
            special_types.append("parallelogram")
        if hasattr(self, 'rectangles') and quad_name in self.rectangles:
            special_types.append("rectangle")
        if hasattr(self, 'squares') and quad_name in self.squares:
            special_types.append("square")
        if hasattr(self, 'rhombi') and quad_name in self.rhombi:
            special_types.append("rhombus")
        if hasattr(self, 'trapezoids') and quad_name in self.trapezoids:
            special_types.append("trapezoid")

        if special_types:
            report += f"Quadrilateral {quad_name} is a {', '.join(special_types)}.\n"

        # Check if area variable exists
        if quad_name in self.quad_areas:
            report += f"Area variable for quadrilateral {quad_name} exists in the system.\n"

            # If solver is satisfiable, get current value
            if self.solver.check() == sat:
                model = self.solver.model()
                try:
                    area_val = float(model.eval(self.quad_areas[quad_name]).as_decimal(10).rstrip('?'))
                    report += f"Current calculated area: {area_val}\n\n"

                    if abs(area_val - expected_value) >= 1e-8:
                        report += f"This doesn't match the expected value {expected_value}.\n\n"
                except Exception as e:
                    report += f"Error evaluating area: {str(e)}\n\n"
        else:
            report += f"No area variable for quadrilateral {quad_name} has been defined.\n"
            report += "You need to establish this through appropriate theorems (like parallelogram_area_formula_common).\n\n"

        # Check if height data exists
        if quad_name in self.quad_heights:
            report += f"Height variable for quadrilateral {quad_name} exists in the system.\n"

            if self.solver.check() == sat:
                model = self.solver.model()
                try:
                    height_val = float(model.eval(self.quad_heights[quad_name]).as_decimal(10).rstrip('?'))
                    report += f"Height of quadrilateral: {height_val}\n"
                except Exception as e:
                    report += f"Error evaluating height: {str(e)}\n"
        else:
            report += f"No height variable for quadrilateral {quad_name} has been defined.\n"
            report += "For area calculation, you typically need to establish a height (using altitude theorems).\n\n"

        # Check for altitude/base data
        if hasattr(self, 'altitudes') and quad_name in self.altitudes:
            report += f"Altitude(s) for quadrilateral {quad_name}: {self.altitudes[quad_name]}\n"
        else:
            report += f"No altitude has been established for quadrilateral {quad_name}.\n"
            report += "For area calculation, you typically need to establish an altitude.\n\n"

        # Report on side lengths if available
        report += "Side lengths of quadrilateral:\n"
        sides_found = 0
        for i in range(len(quad_name)):
            side = quad_name[i] + quad_name[(i + 1) % len(quad_name)]
            normalized_side = self.normalize_line_name(side)
            length_var_name = f"length_{normalized_side}"

            if length_var_name in self.lengths:
                sides_found += 1
                if self.solver.check() == sat:
                    model = self.solver.model()
                    try:
                        length_val = float(model.eval(self.lengths[length_var_name]).as_decimal(10).rstrip('?'))
                        report += f"  Side {side}: {length_val}\n"
                    except Exception as e:
                        report += f"  Side {side}: Error evaluating length - {str(e)}\n"
            else:
                report += f"  Side {side}: Not explicitly defined\n"

        if sides_found == 0:
            report += "  No side lengths explicitly defined for this quadrilateral.\n"
        report += "\n"

        # Find theorems relevant to this quadrilateral
        report += f"\nTheorems related to quadrilateral {quad_name} in your proof:\n"
        report += "-" * 60 + "\n"
        related_theorems = []

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if the quadrilateral is mentioned in the conclusions
            for conclusion in theorem_info["conclusions"]:
                if f"AreaOfQuadrilateral({quad_name})" in conclusion:
                    is_related = True
                    break

            # Check if mentioned in the premise
            if quad_name in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(quad_name in arg for arg in theorem_info["args"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        if related_theorems:
            for theorem in related_theorems:
                report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n"
                report += f"  Conclusion: {theorem['conclusion']}\n\n"
        else:
            report += f"No theorems directly involving quadrilateral {quad_name} were found in your proof.\n\n"

        # Add solver constraints related to this goal
        report += "Solver constraints directly related to this goal:\n"
        report += "-" * 60 + "\n"

        area_var_name = f"areaQuadr_{quad_name}" if quad_name in self.quad_areas else None

        relevant_constraints = []
        for c in self.solver.assertions():
            c_str = str(c)
            if area_var_name and area_var_name in c_str:
                relevant_constraints.append(c_str)
            elif f"quad_{quad_name}" in c_str or quad_name in c_str:
                relevant_constraints.append(c_str)

        if relevant_constraints:
            for i, constraint in enumerate(relevant_constraints):
                report += f"{i + 1}. {constraint}\n"
            report += "\n"
        else:
            report += "No direct constraints found involving this quadrilateral's area.\n\n"

        # Add an explanation based on the solver state
        report += "Diagnosis:\n"
        report += "-" * 60 + "\n"

        if solver_state == "unsatisfiable":
            report += "The solver found the constraints to be contradictory. This means your proof contains\n"
            report += "inconsistent constraints that cannot be satisfied simultaneously.\n\n"
            report += "Possible causes:\n"
            report += "1. Incorrect quadrilateral properties or measurements in premises\n"
            report += "2. Improper theorem application\n"
            report += "3. Conclusions that contradict earlier assertions\n"
            report += "4. Errors in the area formula application\n\n"
        elif solver_state == "incompatible":
            report += f"The geometric constraints in your proof don't allow the area of {quad_name} to be {expected_value}.\n"
            report += "This means your proof implies a different area than expected.\n\n"
            report += "Check that:\n"
            report += "1. Your altitude and base values are correctly specified\n"
            report += "2. You've correctly identified the quadrilateral in question\n"
            report += "3. The correct area formula is being applied\n"
        else:  # multiple_values
            report += f"Your proof doesn't uniquely determine the area of quadrilateral {quad_name}.\n"
            report += "Multiple solutions are possible with the current constraints.\n"
            if alt_value is not None:
                report += f"It could be {expected_value} but also {alt_value}\n\n"
            report += "You need to add more constraints by applying additional theorems.\n"
            report += "Focus on fixing the dimensions of the quadrilateral or establishing specific relationships.\n"

        return report
    def generate_arc_length_analysis_report(self, arc_token, expected_value, alt_value=None,
                                            solver_state="multiple_values"):
        """Generate a detailed report for arc length goals that couldn't be verified."""

        # Create the report content as a string
        report = f"Analysis Report for {self.question_name}\n"
        report += "=" * 60 + "\n\n"
        report += f"Goal: Length of arc {arc_token}\n"
        report += f"Expected value: {expected_value}\n\n"

        # Extract points involved in the arc
        goal_points = list(arc_token)

        # Check if the arc exists in our geometry
        normalized_arc = self.normalize_arc(arc_token)
        arc_var_name = f"arc_{normalized_arc}"

        if arc_var_name in self.arcs:
            report += f"Arc {arc_token} is defined in the system.\n"
            arc_var = self.arcs[arc_var_name]

            # If solver is satisfiable, get current value
            if self.solver.check() == sat:
                model = self.solver.model()
                try:
                    arc_val = float(model.eval(arc_var).as_decimal(10).rstrip('?'))
                    report += f"Current measure of arc {arc_token}: {arc_val}°\n\n"
                except Exception as e:
                    report += f"Error evaluating arc measure: {str(e)}\n\n"
        else:
            report += f"Arc {arc_token} is not defined in the system.\n"
            report += "You need to establish this arc through theorems before calculating its length.\n\n"

        # Check for radius information
        circle_center = arc_token[0]  # Usually the first letter of the arc is the circle center
        if circle_center in self.circle_radii:
            report += f"Circle {circle_center} has a defined radius.\n"
            radius_var = self.circle_radii[circle_center]

            if self.solver.check() == sat:
                model = self.solver.model()
                try:
                    radius_val = float(model.eval(radius_var).as_decimal(10).rstrip('?'))
                    report += f"Radius of circle {circle_center}: {radius_val}\n"

                    # If we have both arc measure and radius, compute expected arc length
                    if arc_var_name in self.arcs:
                        arc_val = float(model.eval(self.arcs[arc_var_name]).as_decimal(10).rstrip('?'))
                        import math
                        computed_length = (arc_val / 180) * math.pi * radius_val
                        report += f"Computed arc length: {computed_length}\n"
                        if abs(computed_length - expected_value) >= 1e-8:
                            report += f"This doesn't match expected value {expected_value}.\n"
                except Exception as e:
                    report += f"Error evaluating radius: {str(e)}\n"
        else:
            report += f"Circle {circle_center} does not have a defined radius.\n"
            report += "Arc length calculation requires both arc measure and circle radius.\n\n"

        # Find theorems relevant to this arc
        report += f"\nTheorems related to arc {arc_token} in your proof:\n"
        report += "-" * 60 + "\n"
        related_theorems = []

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if the arc is mentioned in the conclusions
            for conclusion in theorem_info["conclusions"]:
                if f"MeasureOfArc({arc_token})" in conclusion or f"LengthOfArc({arc_token})" in conclusion:
                    is_related = True
                    break

            # Check if mentioned in the premise
            if arc_token in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(arc_token in arg for arg in theorem_info["args"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        if related_theorems:
            for theorem in related_theorems:
                report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n"
                report += f"  Conclusion: {theorem['conclusion']}\n\n"
        else:
            report += f"No theorems directly involving arc {arc_token} were found in your proof.\n\n"

        # Add solver constraints related to this goal
        report += "Solver constraints directly related to this goal:\n"
        report += "-" * 60 + "\n"

        length_var_name = f"lengthArc_{normalized_arc}"

        relevant_constraints = []
        for c in self.solver.assertions():
            c_str = str(c)
            if arc_var_name in c_str or length_var_name in c_str:
                relevant_constraints.append(c_str)

        if relevant_constraints:
            for i, constraint in enumerate(relevant_constraints):
                report += f"{i + 1}. {constraint}\n"
            report += "\n"
        else:
            report += "No direct constraints found involving this arc's measure or length.\n\n"

        # Add an explanation based on the solver state
        report += "Diagnosis:\n"
        report += "-" * 60 + "\n"

        if solver_state == "unsatisfiable":
            report += "The solver found the constraints to be contradictory. This means your proof contains\n"
            report += "inconsistent constraints that cannot be satisfied simultaneously.\n\n"
            report += "Possible causes:\n"
            report += "1. Incorrect arc or radius values in premises\n"
            report += "2. Improper theorem application\n"
            report += "3. Conclusions that contradict earlier assertions\n"
            report += "4. Errors in the arc length formula application\n\n"
        elif solver_state == "incompatible":
            report += f"The geometric constraints in your proof don't allow the arc length of {arc_token} to be {expected_value}.\n"
            report += "This means your proof implies a different arc length than expected.\n\n"
            report += "Check that:\n"
            report += "1. Your arc measure and radius values are correctly specified\n"
            report += "2. You've correctly identified the arc in question\n"
            report += "3. There are no errors in your arc length calculations\n"
        else:  # multiple_values
            report += f"Your proof doesn't uniquely determine the length of arc {arc_token}.\n"
            report += "Multiple solutions are possible with the current constraints.\n"
            if alt_value is not None:
                report += f"It could be {expected_value} but also {alt_value}\n\n"
            report += "You need to add more constraints by applying additional theorems.\n"
            report += "Focus on fixing the measure of the arc and/or the radius of the circle.\n"

        return report
    def generate_sum_analysis_report(self, line1, line2, expected_value, alt_value=None,
                                     solver_state="multiple_values"):
        """Generate a detailed report for sum goals that couldn't be verified."""

        # Create the report content as a string
        report = f"Analysis Report for {self.question_name}\n"
        report += "=" * 60 + "\n\n"
        report += f"Goal: Sum of lines {line1} + {line2}\n"
        report += f"Expected value: {expected_value}\n\n"

        # Extract points involved in the goal lines
        goal_points = list(set(line1 + line2))

        # Check if the lines exist in our geometry
        report += "Analysis of line segments:\n"
        report += "-" * 60 + "\n"

        # Get or create length variables
        len1_var = self.add_length(line1[0], line1[1])
        len2_var = self.add_length(line2[0], line2[1])

        # Check if the solver is satisfiable
        if self.solver.check() == sat:
            model = self.solver.model()

            try:
                # Get current values from the model
                len1_val = float(model.eval(len1_var).as_decimal(10).rstrip('?'))
                len2_val = float(model.eval(len2_var).as_decimal(10).rstrip('?'))

                report += f"Length of {line1}: {len1_val}\n"
                report += f"Length of {line2}: {len2_val}\n"

                computed_value = len1_val + len2_val
                report += f"Computed sum: {line1} + {line2} = {computed_value}\n\n"

                epsilon = 1e-8
                if abs(computed_value - expected_value) >= epsilon:
                    report += f"Error: Computed sum {computed_value} doesn't match expected {expected_value}\n"
                    report += "This suggests an inconsistency between your proof and the expected answer.\n\n"

                # Check if these lengths are uniquely determined
                report += "Checking uniqueness of line lengths:\n"

                # Check if line1 can have different values
                temp_solver1 = Solver()
                for c in self.solver.assertions():
                    temp_solver1.add(c)

                epsilon = 1e-8
                temp_solver1.add(Or(len1_var < len1_val - epsilon, len1_var > len1_val + epsilon))

                if temp_solver1.check() == sat:
                    alt_model = temp_solver1.model()
                    alt_len1 = float(alt_model.eval(len1_var).as_decimal(10).rstrip('?'))
                    report += f"- Line {line1} is not uniquely determined (could also be {alt_len1})\n"
                else:
                    report += f"- Line {line1} is uniquely determined to be {len1_val}\n"

                # Check if line2 can have different values
                temp_solver2 = Solver()
                for c in self.solver.assertions():
                    temp_solver2.add(c)

                temp_solver2.add(Or(len2_var < len2_val - epsilon, len2_var > len2_val + epsilon))

                if temp_solver2.check() == sat:
                    alt_model = temp_solver2.model()
                    alt_len2 = float(alt_model.eval(len2_var).as_decimal(10).rstrip('?'))
                    report += f"- Line {line2} is not uniquely determined (could also be {alt_len2})\n"
                else:
                    report += f"- Line {line2} is uniquely determined to be {len2_val}\n"

                # Check if the sum itself can be different while satisfying all constraints
                temp_solver3 = Solver()
                for c in self.solver.assertions():
                    temp_solver3.add(c)

                # We want to check if len1 + len2 can have a different value
                temp_solver3.add(Or(
                    len1_var + len2_var < expected_value - epsilon,
                    len1_var + len2_var > expected_value + epsilon
                ))

                if temp_solver3.check() == sat:
                    alt_model = temp_solver3.model()
                    alt_len1 = float(alt_model.eval(len1_var).as_decimal(10).rstrip('?'))
                    alt_len2 = float(alt_model.eval(len2_var).as_decimal(10).rstrip('?'))
                    alt_sum = alt_len1 + alt_len2

                    report += f"\nThe sum {line1} + {line2} is not uniquely determined.\n"
                    report += f"It could be {computed_value} but also {alt_sum}.\n"
                    report += f"Alternative values: {line1} = {alt_len1}, {line2} = {alt_len2}\n\n"
                else:
                    report += f"\nThe sum {line1} + {line2} is uniquely determined to be {computed_value}.\n\n"

            except Exception as e:
                report += f"Error evaluating line lengths: {str(e)}\n\n"

        # Try to find triangles or other shapes that might explain the sum
        report += "Geometric relationships that might explain this sum:\n"
        report += "-" * 60 + "\n"

        # Check if the lines are sides of a triangle
        triangles_containing_both_lines = []
        triangles_containing_either_line = []

        for tri in self.polygons:
            if len(tri) == 3:  # It's a triangle
                if (line1[0] in tri and line1[1] in tri) and (line2[0] in tri and line2[1] in tri):
                    triangles_containing_both_lines.append(tri)
                elif (line1[0] in tri and line1[1] in tri) or (line2[0] in tri and line2[1] in tri):
                    triangles_containing_either_line.append(tri)

        if triangles_containing_both_lines:
            report += "Triangles containing both lines:\n"
            for tri in triangles_containing_both_lines:
                report += f"- Triangle {tri}"
                if tri in self.right_triangles:
                    report += " (right triangle)"
                if hasattr(self, "isosceles_triangles") and tri in self.isosceles_triangles:
                    report += " (isosceles triangle)"
                report += "\n"
        else:
            report += "No triangles found containing both lines.\n"

        if triangles_containing_either_line:
            report += "\nTriangles containing either line:\n"
            for tri in triangles_containing_either_line:
                report += f"- Triangle {tri} contains "
                if line1[0] in tri and line1[1] in tri:
                    report += f"line {line1}"
                elif line2[0] in tri and line2[1] in tri:
                    report += f"line {line2}"
                if tri in self.right_triangles:
                    report += " (right triangle)"
                if hasattr(self, "isosceles_triangles") and tri in self.isosceles_triangles:
                    report += " (isosceles triangle)"
                report += "\n"

        # Check if the points are collinear, suggesting the sum is part of a longer line
        might_be_collinear = False
        collinear_explanation = ""

        common_point = None
        for p in line1:
            if p in line2:
                common_point = p
                break

        if common_point is not None:
            # Lines share a point, check if all points are collinear
            p1 = line1[0] if line1[1] == common_point else line1[1]
            p2 = line2[0] if line2[1] == common_point else line2[1]

            # Check if p1-common_point-p2 are collinear
            all_points = p1 + common_point + p2
            for fact in self.collinear_facts:
                fact_str = ''.join(fact)
                if all(p in fact_str for p in all_points):
                    might_be_collinear = True
                    collinear_explanation = f"Points {p1}, {common_point}, and {p2} are collinear."
                    break

            if might_be_collinear:
                report += f"\nThese segments appear to form a single line through {collinear_explanation}\n"
                report += f"This suggests the sum {line1} + {line2} might represent the length of line {p1}{p2}.\n"

                # Check if we have a length for the combined line
                full_line = self.add_length(p1, p2)
                if self.solver.check() == sat:
                    model = self.solver.model()
                    full_line_val = float(model.eval(full_line).as_decimal(10).rstrip('?'))
                    report += f"Length of full line {p1}{p2}: {full_line_val}\n"

                    # Check if this matches our sum
                    sum_val = len1_val + len2_val if 'len1_val' in locals() and 'len2_val' in locals() else None
                    if sum_val is not None:
                        report += f"Computed sum {line1} + {line2} = {sum_val}\n"

                        if abs(full_line_val - sum_val) < epsilon:
                            report += f"The full line length matches the sum, confirming {line1} + {line2} = {p1}{p2}\n"
                        else:
                            report += f"The full line length {full_line_val} does not match the sum {sum_val}, suggesting additional constraints are needed.\n"

        # Check if the lines might be related through a perimeter calculation
        # First look for a polygon that might contain these lines as sides
        polygons_with_lines = []
        for poly in self.polygons:
            sides_found = 0
            # Check if line1 is a side
            if (line1[0] in poly and line1[1] in poly and
                    any(line1[0] == poly[i] and line1[1] == poly[(i + 1) % len(poly)] or
                        line1[1] == poly[i] and line1[0] == poly[(i + 1) % len(poly)]
                        for i in range(len(poly)))):
                sides_found += 1

            # Check if line2 is a side
            if (line2[0] in poly and line2[1] in poly and
                    any(line2[0] == poly[i] and line2[1] == poly[(i + 1) % len(poly)] or
                        line2[1] == poly[i] and line2[0] == poly[(i + 1) % len(poly)]
                        for i in range(len(poly)))):
                sides_found += 1

            if sides_found > 0:
                polygons_with_lines.append((poly, sides_found))

        if polygons_with_lines:
            report += "\nPolygons containing these lines as sides:\n"
            for poly, sides_count in polygons_with_lines:
                report += f"- Polygon {poly} contains {sides_count} of the lines in the sum\n"

            perimeter_sum_candidates = [poly for poly, sides in polygons_with_lines if sides == 2]
            if perimeter_sum_candidates:
                report += "\nThese lines might be part of the perimeter calculation for:\n"
                for poly in perimeter_sum_candidates:
                    report += f"- Polygon {poly}\n"

        # Find theorems relevant to these lines
        report += f"\nTheorems related to lines {line1} and {line2} in your proof:\n"
        report += "-" * 60 + "\n"
        related_theorems = []

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if the lines are mentioned in the conclusions
            for conclusion in theorem_info["conclusions"]:
                if f"LengthOfLine({line1})" in conclusion or f"LengthOfLine({line2})" in conclusion:
                    is_related = True
                    break

                # Check for sum expressions
                if f"Add(LengthOfLine({line1}),LengthOfLine({line2}))" in conclusion or \
                        f"Add(LengthOfLine({line2}),LengthOfLine({line1}))" in conclusion:
                    is_related = True
                    break

            # Check if mentioned in the premise
            if line1 in theorem_info["premise"] or line2 in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(line1 in arg or line2 in arg for arg in theorem_info["args"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        if related_theorems:
            for theorem in related_theorems:
                report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n"
                report += f"  Conclusion: {theorem['conclusion']}\n\n"
        else:
            report += f"No theorems directly involving lines {line1} or {line2} were found in your proof.\n\n"

        # Add solver constraints related to this goal
        report += "Solver constraints directly related to this goal:\n"
        report += "-" * 60 + "\n"

        len1_var_name = f"length_{self.normalize_line_name(line1)}"
        len2_var_name = f"length_{self.normalize_line_name(line2)}"

        relevant_constraints = []
        for c in self.solver.assertions():
            c_str = str(c)
            if len1_var_name in c_str or len2_var_name in c_str:
                relevant_constraints.append(c_str)

        if relevant_constraints:
            for i, constraint in enumerate(relevant_constraints):
                report += f"{i + 1}. {constraint}\n"
            report += "\n"
        else:
            report += "No direct constraints found involving these lines' lengths.\n\n"

        # Add an explanation based on the solver state
        report += "Diagnosis:\n"
        report += "-" * 60 + "\n"

        if solver_state == "unsatisfiable":
            report += "The solver found the constraints to be contradictory. This means your proof contains\n"
            report += "inconsistent constraints that cannot be satisfied simultaneously.\n\n"
            report += "Possible causes:\n"
            report += "1. Incorrect length values in premises\n"
            report += "2. Improper theorem application\n"
            report += "3. Conclusions that contradict earlier assertions\n"
            report += "4. Errors in the sum or perimeter calculations\n\n"
        elif solver_state == "incompatible":
            report += f"The geometric constraints in your proof don't allow the sum {line1} + {line2} to be {expected_value}.\n"
            report += "This means your proof implies a different sum than expected.\n\n"
            report += "Check that:\n"
            report += "1. Your line length values are correctly specified\n"
            report += "2. You've correctly identified the lines in question\n"
            report += "3. Your theorems about lengths or sums are correctly applied\n"
        else:  # multiple_values
            report += f"Your proof doesn't uniquely determine the sum {line1} + {line2}.\n"
            report += "Multiple solutions are possible with the current constraints.\n"
            if alt_value is not None:
                report += f"It could be {expected_value} but also {alt_value}\n\n"
            report += "You need to add more constraints by applying additional theorems.\n"
            report += "Consider using theorems that fix the individual lengths of these lines,\n"
            report += "such as the Pythagorean theorem, similar triangles, or other geometric relationships.\n"

        return report



    def generate_goal_analysis_report(self, goal_angle, expected, alt_value, solver_state="multiple_values"):
        """Generate a focused report about why the goal couldn't be uniquely determined"""

        # Create the report content as a string
        report = f"Analysis Report for {self.question_name}\n"
        report += "=" * 60 + "\n\n"
        report += f"You tried to find the goal angle {goal_angle}\n\n"

        report += "In the premises you've had:\n"
        report += "-" * 60 + "\n"

        # Extract points involved in the goal angle
        goal_points = list(goal_angle)

        # Get all related facts from our knowledge base
        related_facts = self.collect_related_facts(goal_points)

        if related_facts:
            for category, facts in related_facts.items():
                if facts:  # Only show categories with facts
                    report += f"{category}:\n"
                    for fact in facts:
                        report += f"  - {fact}\n"
                    report += "\n"
        else:
            report += "No facts involving exactly these points " + ", ".join(
                goal_points) + " were found in the premises.\n\n"

        report += f"These are the theorems that have to do with goal {goal_angle} in your proof:\n"
        report += "-" * 60 + "\n"

        # Find theorems that mention the goal or its components
        related_theorems = self.find_related_theorems(goal_angle, goal_points)

        if related_theorems:
            for theorem in related_theorems:
                report += f"Step {theorem['step']} - {theorem['theorem']}({', '.join(theorem['args'])}):\n"
                report += f"  Conclusion: {theorem['conclusion']}\n\n"
        else:
            report += f"None. Your proof doesn't include any theorems that constrain angle {goal_angle}.\n\n"

        # Add solver constraints related to this goal
        report += "Solver constraints directly related to this goal:\n"
        report += "-" * 60 + "\n"

        # Normalize the angle name for looking up in solver
        normalized_angle = self.normalize_angle_name(goal_angle)
        angle_var = self.add_angle(goal_angle[0], goal_angle[1], goal_angle[2])
        angle_var_name = f"angle_{normalized_angle}"

        # More precise constraint filtering - focus only on those directly affecting the angle
        relevant_constraints = []
        for c in self.solver.assertions():
            c_str = str(c)
            # Only include constraints that directly mention the exact angle variable name
            if angle_var_name in c_str:
                # Check for direct relationships with this angle using list of conditions
                patterns = [
                    f"{angle_var_name} " in c_str,
                    f"{angle_var_name}=" in c_str,
                    f"{angle_var_name}+" in c_str,
                    f"{angle_var_name}-" in c_str,
                    f"{angle_var_name}*" in c_str,
                    f"{angle_var_name}/" in c_str
                ]
                if any(patterns):
                    relevant_constraints.append(c_str)

            # Also include constraints that set the angle value
            elif f" == {angle_var_name}" in c_str:
                relevant_constraints.append(c_str)

        if relevant_constraints:
            for i, constraint in enumerate(relevant_constraints):
                report += f"{i + 1}. {constraint}\n"
            report += "\n"
        else:
            report += "No direct constraints found involving this angle.\n\n"

        # Add different explanations based on solver state
        if solver_state == "unsatisfiable":
            report += f"The solver found the constraints to be contradictory when trying to evaluate angle {goal_angle}.\n"
            report += "This means there's an inconsistency in your geometric setup or theorem applications.\n"
            report += "Check for contradictory premises or incorrectly applied theorems.\n"
        elif solver_state == "incompatible":
            report += f"The constraints in your proof are consistent, but don't allow angle {goal_angle} to be {expected}°.\n"
            report += "This means your proof implies a different value for this angle than expected.\n"
        else:  # multiple_values
            report += f"This wasn't enough information to get a unique value for the goal angle {goal_angle}.\n"
            report += "Your proof allows multiple solutions for this angle.\n"
            if alt_value is not None:
                report += f"It could be {expected}° but also {alt_value}°\n"
            report += "You need to add more constraints by applying additional theorems.\n"

        # Write the report to a file (still using the original file writing code)
        import os
        import datetime
        output_dir = "info"
        os.makedirs(output_dir, exist_ok=True)
        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"{output_dir}/{self.question_name}_{timestamp}.txt"
        with open(filename, 'w') as f:
            f.write(report)
        print(f"\nDetailed analysis written to: {filename}")

        # Return the report content as a string
        return report

    def verify_algebraic_goal(self, goal_angle: str, expected: float, epsilon: float = 1e-8) -> tuple:
        """Verify if the angle measure goal is satisfied by the constraints."""
        print(f"\nVerifying goal angle: {goal_angle}")

        # Create a detailed report string
        angle_report = f"Analysis Report for {self.question_name}\n"
        angle_report += "=" * 60 + "\n\n"
        angle_report += f"Goal: Measure of angle {goal_angle}\n"
        angle_report += f"Expected value: {expected}°\n\n"

        goal_var = self.add_angle(goal_angle[0], goal_angle[1], goal_angle[2])

        if self.solver.check() == sat:
            # First check if constraints allow the expected value
            temp_solver1 = Solver()
            for c in self.solver.assertions():
                temp_solver1.add(c)

            # Add constraint that goal_var == expected (within epsilon)
            temp_solver1.add(And(goal_var >= expected - epsilon, goal_var <= expected + epsilon))

            if temp_solver1.check() != sat:
                error_msg = "Failed to prove angle goal: constraints don't allow the expected value."
                angle_report += f"Error: Constraints don't allow the expected angle {expected}°\n"
                angle_report += "The geometric constraints are incompatible with the expected answer.\n"

                # Generate a detailed report for this case
                detailed_report = self.generate_goal_analysis_report(goal_angle, expected, None, "incompatible")
                angle_report += f"\n{detailed_report}\n"

                print(f"Error: Constraints don't allow the expected angle {expected}")
                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message=error_msg,
                    details=f"Goal was: MeasureOfAngle({goal_angle}) = {expected}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")
                if error.details:
                    print("Details:", error.details)

                # Write report to file
                self.write_failure_report(f"angle_{goal_angle}", angle_report)
                return False, angle_report  # Return just the error message, not the full report

            # Now check if any other value is allowed
            temp_solver2 = Solver()
            for c in self.solver.assertions():
                temp_solver2.add(c)

            # Add constraint: goal_var != expected (outside epsilon range)
            temp_solver2.add(Or(goal_var < expected - epsilon, goal_var > expected + epsilon))

            if temp_solver2.check() == sat:
                alt_model = temp_solver2.model()
                alt_value = float(alt_model.eval(goal_var).as_decimal(10).rstrip('?'))

                error_msg = "Failed to prove angle goal: constraints allow multiple values."
                angle_report += f"Error: The proof doesn't uniquely determine angle {goal_angle}.\n"
                angle_report += f"It could be {expected}° but also {alt_value}°\n\n"
                angle_report += "The proof needs additional constraints to uniquely determine this angle.\n"

                # Collect more detailed information about why the goal couldn't be uniquely determined
                detailed_report = self.generate_goal_analysis_report(goal_angle, expected, alt_value, "multiple_values")
                angle_report += f"\n{detailed_report}\n"

                print(f"Error: The proof doesn't uniquely determine angle {goal_angle}.")
                print(f"Multiple solutions exist for this angle.")

                error = GeometricError(
                    tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                    message=error_msg,
                    details=f"Goal was: MeasureOfAngle({goal_angle}) = {expected}, but could also be {alt_value}"
                )
                print(f"\nError in {error.tier.name}: {error.message}")
                if error.details:
                    print("Details:", error.details)

                # Write report to file
                self.write_failure_report(f"angle_{goal_angle}", angle_report)
                return False, angle_report  # Return just the error message, not the full report

            # If we get here, the constraints uniquely determine the value
            model = self.solver.model()
            val = model.eval(goal_var)
            val_str = val.as_decimal(10)
            if val_str.endswith('?'):
                val_str = val_str[:-1]
            computed = float(val_str)

            print(f"Solver gives {goal_angle} = {computed}°")
            print(f"Success: Angle {goal_angle} is uniquely determined to be {expected}.")
            return True, ""
        else:
            error_msg = "Failed to prove angle goal: solver is unsatisfiable."
            angle_report += "Error: Solver constraints unsatisfiable. The geometric constraints are inconsistent.\n"

            # Generate a detailed report for unsatisfiable case
            detailed_report = self.generate_goal_analysis_report(goal_angle, expected, None, "unsatisfiable")
            angle_report += f"\n{detailed_report}\n"

            print("Solver is unsat when evaluating goal angle.")
            error = GeometricError(
                tier=ErrorTier.TIER3_GOAL_NOT_REACHED,
                message=error_msg,
                details=f"Goal was: MeasureOfAngle({goal_angle}) = {expected}"
            )
            print(f"\nError in {error.tier.name}: {error.message}")
            if error.details:
                print("Details:", error.details)

            # Write report to file
            self.write_failure_report(f"angle_{goal_angle}", angle_report)
            return False, error_msg  # Return just the error message, not the full report



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
            "cosine_theorem",
            "circle_property_circular_power_chord_and_chord",
            "round_angle",
            "flat_angle",
            "altitude_of_triangle_judgment",
            "triangle_area_formula_common",
            "perpendicular_bisector_property_distance_equal",
            "parallelogram_judgment_parallel_and_parallel",
            "vertical_angle",
            "isosceles_triangle_judgment_angle_equal",
            "incenter_of_triangle_judgment_intersection",
            "median_of_triangle_judgment",
            "right_triangle_property_length_of_median",
            "congruent_triangle_property_line_equal",
            "congruent_triangle_property_angle_equal"
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


        # In the adding_conclution method

        # In the adding_conclution method
        elif theorem_name == "right_triangle_property_length_of_median":
            version = args[0]
            if version == "1":
                # Expected conclusion: ["Equal(Mul(LengthOfLine(EM),2),LengthOfLine(BC))"]
                match = re.search(r'Equal\(Mul\(LengthOfLine\((\w+)\),2\),LengthOfLine\((\w+)\)\)', conclusions[0])
                if not match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Invalid conclusion format for right_triangle_property_length_of_median",
                        details="Expected format: Equal(Mul(LengthOfLine(median),2),LengthOfLine(hypotenuse))"
                    )

                median_line = match.group(1)  # "EM"
                hypotenuse = match.group(2)  # "BC"

                # Add the constraint: median_length * 2 = hypotenuse_length
                median_length = self.add_length(median_line[0], median_line[1])
                hypotenuse_length = self.add_length(hypotenuse[0], hypotenuse[1])

                self.solver.add(median_length * 2 == hypotenuse_length)
                print(
                    f"Added right triangle median property: 2 * LengthOfLine({median_line}) = LengthOfLine({hypotenuse})")

                return None

        # Then add these handlers in the if-elif chain:
        elif theorem_name == "congruent_triangle_property_line_equal":
            version = args[0]
            if version == "1":
                match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', conclusions[0])
                if match:
                    line1, line2 = match.groups()
                    line1_var = self.add_length(line1[0], line1[1])
                    line2_var = self.add_length(line2[0], line2[1])
                    self.solver.add(line1_var == line2_var)
                    print(f"Added congruent triangle property: LengthOfLine({line1}) = LengthOfLine({line2})")
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Conclusion format error for congruent_triangle_property_line_equal",
                        details=f"Expected format: Equal(LengthOfLine(XX),LengthOfLine(YY)) but got {conclusions[0]}"
                    )

        elif theorem_name == "congruent_triangle_property_angle_equal":
            version = args[0]
            if version == "1":
                match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\)', conclusions[0])
                if match:
                    angle1, angle2 = match.groups()
                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])
                    self.solver.add(angle1_var == angle2_var)
                    print(f"Added congruent triangle property: MeasureOfAngle({angle1}) = MeasureOfAngle({angle2})")
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Conclusion format error for congruent_triangle_property_angle_equal",
                        details=f"Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY)) but got {conclusions[0]}"
                    )


        elif theorem_name == "median_of_triangle_judgment":

            version = args[0]

            if version == "1":

                # Expected conclusion: ["IsMedianOfTriangle(EM,EBC)"]

                median_match = re.search(r'IsMedianOfTriangle\((\w+),(\w+)\)', conclusions[0])

                if not median_match:
                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Invalid conclusion format for median_of_triangle_judgment",

                        details="Expected format: IsMedianOfTriangle(line,triangle)"

                    )

                median_line = median_match.group(1)  # "EM"

                triangle = median_match.group(2)  # "EBC"

                # Store the median information

                if not hasattr(self, "medians"):
                    self.medians = []

                self.medians.append((median_line, triangle))

                print(f"Recorded median: IsMedianOfTriangle({median_line},{triangle})")

                return None

        elif theorem_name == "incenter_of_triangle_judgment_intersection":
            incenter_match = re.search(r'IsIncenterOfTriangle\((\w+),(\w+)\)', conclusions[0])
            if not incenter_match:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message="Invalid conclusion format for incenter_of_triangle_judgment_intersection",
                    details="Expected format: IsIncenterOfTriangle(point,triangle)"
                )

            point, triangle = incenter_match.groups()

            # Store the incenter fact for future reference
            if not hasattr(self, "incenters"):
                self.incenters = {}
            self.incenters[triangle] = point

            print(f"Recorded incenter fact: {point} is the incenter of triangle {triangle}")
            return None


        elif theorem_name == "vertical_angle":
            version = args[0]
            if version == "1":
                # Expected conclusion: "Equal(MeasureOfAngle(DEB),MeasureOfAngle(CEA))"
                match = re.search(
                    r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)',
                    conclusions[0]
                )

                if match:
                    angle1, angle2 = match.groups()

                    # Get (or create) angle variables
                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                    # Add the equality constraint
                    self.solver.add(angle1_var == angle2_var)

                    print(f"Added vertical angle constraint: {angle1} = {angle2}")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Conclusion format error for vertical_angle",
                        details=f"Expected format: Equal(MeasureOfAngle(XXX),MeasureOfAngle(YYY)) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for vertical_angle"
                )




        elif theorem_name == "isosceles_triangle_judgment_angle_equal":

            # Expected theorem call: isosceles_triangle_judgment_angle_equal(1, triangle)

            # where triangle is a triangle name (e.g., "ABE")

            tri = args[1].strip()

            # Record that the triangle is isosceles by adding it and all its cyclic rotations

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

            # Extract the equal angles from the premise to determine which sides should be equal

            angle_equal_match = re.search(r'Equal\(MeasureOfAngle\((\w{3})\),\s*MeasureOfAngle\((\w{3})\)\)', premise)

            if angle_equal_match:

                angle1, angle2 = angle_equal_match.groups()

                # Function to get the side opposite to an angle in a triangle

                def get_opposite_side(triangle, angle):

                    # The angle is specified by three points, where the middle point is the vertex

                    # The opposite side is formed by the other two points in the triangle that aren't the vertex

                    vertex = angle[1]  # Middle character is the vertex

                    return "".join(sorted([p for p in triangle if p != vertex]))

                # Get the opposite sides to the equal angles

                side1 = get_opposite_side(tri, angle1)

                side2 = get_opposite_side(tri, angle2)

                # Create length variables for both sides

                if len(side1) == 2 and len(side2) == 2:
                    side1_var = self.add_length(side1[0], side1[1])

                    side2_var = self.add_length(side2[0], side2[1])

                    # Add constraint that these sides are equal

                    self.solver.add(side1_var == side2_var)

                    print(f"Added isosceles triangle side equality: {side1} = {side2}")

            return None

        elif theorem_name == "parallelogram_judgment_parallel_and_parallel":
            version = args[0]
            if version == "1":
                # Check if we have at least the quadrilateral name
                if len(args) < 2:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Missing quadrilateral name for parallelogram_judgment_parallel_and_parallel",
                        details="Expected parallelogram_judgment_parallel_and_parallel(1, quadrilateral)"
                    )

                quad_name = args[1].strip()  # e.g., "BCDF"

                # Parse the premise to check polygon and parallel conditions
                premise_parts = premise.split('&')

                # First check if the polygon exists
                polygon_part = premise_parts[0].strip() if premise_parts else ""
                polygon_match = re.match(r'Polygon\((\w+)\)', polygon_part)

                if not polygon_match or polygon_match.group(1) != quad_name:
                    return GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message=f"Missing or incorrect polygon premise for {quad_name}",
                        details=f"Expected Polygon({quad_name}) in premise"
                    )

                # Check for parallel sides
                if len(premise_parts) < 3:
                    return GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Missing parallel sides conditions",
                        details="Need two ParallelBetweenLine statements in premise"
                    )

                # Parse the two parallel conditions
                parallel_matches = [re.match(r'ParallelBetweenLine\((\w+),(\w+)\)', part.strip())
                                    for part in premise_parts[1:3]]

                if not all(parallel_matches):
                    return GeometricError(
                        tier=ErrorTier.TIER2_PREMISE,
                        message="Invalid parallel lines format in premise",
                        details="Expected format: ParallelBetweenLine(XX,YY)"
                    )

                # Verify that these parallel relations are recorded
                parallel_pairs = [(m.group(1), m.group(2)) for m in parallel_matches if m]
                for pair in parallel_pairs:
                    possible_pairs = [
                        pair,
                        (pair[1], pair[0]),
                        (pair[0][::-1], pair[1]),
                        (pair[0], pair[1][::-1]),
                        (pair[0][::-1], pair[1][::-1]),
                        (pair[1][::-1], pair[0]),
                        (pair[1], pair[0][::-1]),
                        (pair[1][::-1], pair[0][::-1])
                    ]

                    if not any(p in self.parallel_pairs or p[::-1] in self.parallel_pairs for p in possible_pairs):
                        return GeometricError(
                            tier=ErrorTier.TIER2_PREMISE,
                            message=f"Parallel relation {pair} not established",
                            details=f"Known parallel pairs: {self.parallel_pairs}"
                        )

                # All checks passed, now record the quadrilateral as a parallelogram
                # Add the parallelogram and its cyclic variations to the parallelograms set
                if not hasattr(self, 'parallelograms'):
                    self.parallelograms = set()

                # Get all cyclic variations of the parallelogram
                parallelogram_variations = get_cyclic_variations(quad_name)
                self.parallelograms.update(parallelogram_variations)

                print(f"Added {quad_name} as a parallelogram based on parallel sides")
                return None
            elif version == "2":
                # Handle version 2 if needed
                print("Version 2 for parallelogram_judgment_parallel_and_parallel not implemented")
                return None


        elif theorem_name == "perpendicular_bisector_property_distance_equal":
            version = args[0]
            if version == "1":
                # Parse conclusion: "Equal(LengthOfLine(EA),LengthOfLine(EC))"
                match = re.search(r'Equal\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)', conclusions[0])

                if match:
                    segment1, segment2 = match.groups()  # e.g., "EA", "EC"

                    # Get (or create) length variables for both segments
                    length1 = self.add_length(segment1[0], segment1[1])
                    length2 = self.add_length(segment2[0], segment2[1])

                    # Add the equality constraint
                    self.solver.add(length1 == length2)

                    print(
                        f"Added perpendicular bisector property constraint: LengthOfLine({segment1}) = LengthOfLine({segment2})")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Conclusion format error for perpendicular_bisector_property_distance_equal",
                        details=f"Expected Equal(LengthOfLine(...),LengthOfLine(...)) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for perpendicular_bisector_property_distance_equal"
                )




        elif theorem_name == "triangle_area_formula_common":

            version = args[0]

            if version == "1":

                # Parse conclusion: "Equal(AreaOfTriangle(DCA),Mul(HeightOfTriangle(DCA),LengthOfLine(CA),1/2))"

                match = re.search(

                    r'Equal\(AreaOfTriangle\((\w+)\),Mul\(HeightOfTriangle\(\1\),LengthOfLine\((\w+)\),(\d+/\d+)\)\)',

                    conclusions[0]

                )

                if match:

                    triangle, base, factor_str = match.groups()

                    # Get or create area variable

                    normalized_triangle = ''.join(sorted(triangle))  # Normalize alphabetically as requested

                    if normalized_triangle not in self.triangle_areas:
                        self.triangle_areas[normalized_triangle] = Real(f"areaTriangle_{normalized_triangle}")

                        self.solver.add(self.triangle_areas[normalized_triangle] >= 0)

                    area_var = self.triangle_areas[normalized_triangle]

                    # Create height variable if it doesn't exist

                    if not hasattr(self, "triangle_heights"):
                        self.triangle_heights = {}

                    if triangle not in self.triangle_heights:

                        height_var = Real(f"heightTriangle_{triangle}")

                        self.triangle_heights[triangle] = height_var

                        self.solver.add(height_var >= 0)

                        print(f"Created height variable for triangle {triangle}")

                    else:

                        height_var = self.triangle_heights[triangle]

                    # Get base length variable

                    base_var = self.add_length(base[0], base[1])

                    # Parse the factor (usually 1/2)

                    try:

                        from fractions import Fraction

                        factor_val = float(Fraction(factor_str))

                    except Exception as e:

                        print(f"Error parsing factor {factor_str}: {e}, defaulting to 0.5")

                        factor_val = 0.5

                    # Add area formula constraint: area = (1/2) * height * base

                    self.solver.add(area_var == factor_val * height_var * base_var)

                    print(
                        f"Added triangle area constraint: AreaOfTriangle({triangle}) = {factor_val} * HeightOfTriangle({triangle}) * LengthOfLine({base})")

                    return None

                else:

                    return GeometricError(

                        tier=ErrorTier.TIER1_THEOREM_CALL,

                        message="Conclusion format error for triangle_area_formula_common",

                        details=f"Expected pattern not found in: {conclusions[0]}"

                    )

            else:

                return GeometricError(

                    tier=ErrorTier.TIER1_THEOREM_CALL,

                    message=f"Unsupported version {version} for triangle_area_formula_common"

                )




        elif theorem_name == "altitude_of_triangle_judgment":
            version = args[0]
            if version == "1":
                # Parse conclusion: "IsAltitudeOfTriangle(DN,DAB)"
                match = re.search(r'IsAltitudeOfTriangle\((\w+),(\w+)\)', conclusions[0])

                if match:
                    altitude, triangle = match.groups()

                    # Initialize triangle altitudes dictionary if it doesn't exist
                    if not hasattr(self, "triangle_altitudes"):
                        self.triangle_altitudes = {}

                    # Initialize heights dictionary if it doesn't exist
                    if not hasattr(self, "triangle_heights"):
                        self.triangle_heights = {}

                    # Add altitude information
                    if triangle not in self.triangle_altitudes:
                        self.triangle_altitudes[triangle] = []
                    self.triangle_altitudes[triangle].append(altitude)

                    # Create height variable for this triangle
                    if triangle not in self.triangle_heights:
                        height_var = Real(f"heightTriangle_{triangle}")
                        self.triangle_heights[triangle] = height_var
                        self.solver.add(height_var >= 0)

                        # The height equals the altitude length
                        altitude_length = self.add_length(altitude[0], altitude[1])
                        # Note: In some geometric systems, the altitude might not be the full length
                        # If needed, you might have to compute the height differently
                        self.solver.add(height_var == altitude_length)

                    print(f"Added altitude fact: {altitude} is an altitude of triangle {triangle}")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Conclusion format error for altitude_of_triangle_judgment",
                        details=f"Expected IsAltitudeOfTriangle(...) pattern but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for altitude_of_triangle_judgment"
                )

        elif theorem_name == "round_angle":
            version = args[0]
            if version == "1":
                # Expected conclusion: "Equal(Add(MeasureOfAngle(FBC),MeasureOfAngle(CBF)),360)"
                match = re.search(
                    r'Equal\(Add\(MeasureOfAngle\((\w{3})\),MeasureOfAngle\((\w{3})\)\),360\)',
                    conclusions[0]
                )

                if match:
                    angle1, angle2 = match.groups()

                    # Get (or create) angle variables
                    angle1_var = self.add_angle(angle1[0], angle1[1], angle1[2])
                    angle2_var = self.add_angle(angle2[0], angle2[1], angle2[2])

                    # Add the constraint that the sum of angles equals 360 degrees
                    self.solver.add(angle1_var + angle2_var == 360)

                    print(f"Added round angle constraint: {angle1} + {angle2} = 360°")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Conclusion format error for round_angle",
                        details=f"Expected pattern Equal(Add(MeasureOfAngle(XXX),MeasureOfAngle(YYY)),360) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for round_angle"
                )

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

        elif theorem_name == "flat_angle":
            version = args[0]
            if version == "1":
                # Expected conclusion: "Equal(MeasureOfAngle(BPA),180)"
                match = re.search(
                    r'Equal\(MeasureOfAngle\((\w{3})\),180\)',
                    conclusions[0]
                )

                if match:
                    angle_name = match.group(1)

                    # Get (or create) the angle variable
                    angle_var = self.add_angle(angle_name[0], angle_name[1], angle_name[2])

                    # Add the constraint that this is a straight/flat angle (180 degrees)
                    self.solver.add(angle_var == 180)

                    print(f"Added flat angle constraint: {angle_name} = 180°")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Conclusion format error for flat_angle",
                        details=f"Expected pattern Equal(MeasureOfAngle(XXX),180) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for flat_angle"
                )




        elif theorem_name == "circle_property_circular_power_chord_and_chord":
            version = args[0]
            if version == "1":
                # Parse conclusion: "Equal(Mul(LengthOfLine(ED),LengthOfLine(EC)),Mul(LengthOfLine(EB),LengthOfLine(EA)))"
                match = re.search(
                    r'Equal\(Mul\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\),Mul\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)',
                    conclusions[0]
                )

                if match:
                    segment1, segment2, segment3, segment4 = match.groups()

                    # Get (or create) length variables for the segments
                    length1 = self.add_length(segment1[0], segment1[1])
                    length2 = self.add_length(segment2[0], segment2[1])
                    length3 = self.add_length(segment3[0], segment3[1])
                    length4 = self.add_length(segment4[0], segment4[1])

                    # Add the power of circle constraint: ED × EC = EB × EA
                    self.solver.add(length1 * length2 == length3 * length4)

                    print(f"Added circle power constraint: {segment1} × {segment2} = {segment3} × {segment4}")
                    return None
                else:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL,
                        message="Conclusion format error for circle_property_circular_power_chord_and_chord",
                        details=f"Expected pattern Equal(Mul(...),Mul(...)) but got {conclusions[0]}"
                    )
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL,
                    message=f"Unsupported version {version} for circle_property_circular_power_chord_and_chord"
                )



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

                    # Look up the ratio variable

                    if norm_tris not in self.triangle_ratios:
                        var_name = f"ratio_{norm_tris[0]}_{norm_tris[1]}"

                        self.triangle_ratios[norm_tris] = Real(var_name)

                    ratio = self.triangle_ratios[norm_tris]

                    # Add the original constraint

                    line1_var = self.add_length(line1[0], line1[1])

                    line2_var = self.add_length(line2[0], line2[1])

                    self.solver.add(line1_var == line2_var * ratio)

                    # NEW CODE: Try to determine the ratio value if possible

                    if self.solver.check() == sat:

                        model = self.solver.model()

                        # Check if line1 and line2 have uniquely determined values

                        try:

                            # Get current values

                            len1_val = float(model.eval(line1_var).as_decimal(10).rstrip('?'))

                            len2_val = float(model.eval(line2_var).as_decimal(10).rstrip('?'))

                            # Create temporary solvers to check if these values are unique

                            temp_solver1 = Solver()

                            for c in self.solver.assertions():
                                temp_solver1.add(c)

                            epsilon = 1e-8

                            temp_solver1.add(Or(

                                line1_var < len1_val - epsilon,

                                line1_var > len1_val + epsilon

                            ))

                            temp_solver2 = Solver()

                            for c in self.solver.assertions():
                                temp_solver2.add(c)

                            temp_solver2.add(Or(

                                line2_var < len2_val - epsilon,

                                line2_var > len2_val + epsilon

                            ))

                            # If both sides have unique values and second side is non-zero

                            if temp_solver1.check() == unsat and temp_solver2.check() == unsat and len2_val > epsilon:

                                computed_ratio = len1_val / len2_val

                                # Check if this ratio makes sense

                                temp_solver3 = Solver()

                                for c in self.solver.assertions():
                                    temp_solver3.add(c)

                                # Add the computed ratio as a constraint

                                temp_solver3.add(ratio == computed_ratio)

                                if temp_solver3.check() == sat:
                                    # This ratio is consistent with existing constraints

                                    self.solver.add(ratio == computed_ratio)

                                    print(f"Determined similarity ratio: {computed_ratio} from {line1}/{line2}")

                        except Exception as e:

                            # Just log and continue - don't disrupt functionality

                            print(f"Note: Could not determine unique ratio: {str(e)}")

                    # Also check if the ratio is constrained by other means

                    if self.solver.check() == sat:

                        model = self.solver.model()

                        try:

                            ratio_val = float(model.eval(ratio).as_decimal(10).rstrip('?'))

                            # Check if the ratio is uniquely determined

                            temp_solver = Solver()

                            for c in self.solver.assertions():
                                temp_solver.add(c)

                            epsilon = 1e-8

                            temp_solver.add(Or(

                                ratio < ratio_val - epsilon,

                                ratio > ratio_val + epsilon

                            ))

                            if temp_solver.check() == unsat:

                                # The ratio is already uniquely determined

                                print(f"Triangle similarity ratio is constrained to: {ratio_val}")

                            else:

                                # Find an alternative value to help with debugging

                                alt_model = temp_solver.model()

                                alt_ratio = float(alt_model.eval(ratio).as_decimal(10).rstrip('?'))

                                print(
                                    f"Triangle similarity ratio not uniquely determined: could be {ratio_val} or {alt_ratio}")

                        except Exception as e:

                            # Just log and continue

                            print(f"Note: Error checking ratio uniqueness: {str(e)}")

                    # Original print statement

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


def verify_geometric_proof(filename: str, print_output = True) -> tuple:
    """Main function to verify a geometric proof"""
    import contextlib
    import sys
    ctx = contextlib.nullcontext() if print_output else contextlib.redirect_stdout(None)
    with ctx:
        try:
            question_match = re.search(r'question[_-]?(\d+)', filename, re.IGNORECASE)
            question_name = f"question_{question_match.group(1)}" if question_match else "unknown_question"
            print(f"Processing {question_name}...")
            with open(filename, 'r') as file:
                content = file.read()

            theorem = GeometricTheorem()
            theorem.question_name = question_name
            result, feedback = theorem.parse_and_verify_proof(content)
            print(f"\nOverall verification {'succeeded' if result else 'failed'}")
            return result, feedback
        except Exception as e:
            print(f"Error: {str(e)}")
            return False, f"Error: {str(e)}"



#/Users/eitan/Desktop/lean/lean_python/questions/the new format for questions after jan_17/new_3_questions/question1/question1_correct
if __name__ == "__main__":
    result, feedback = verify_geometric_proof(
        "/Users/eitan/Desktop/lean/lean_python/questions/the new format for questions after jan_17/new_45_questions/question_3434/question3434_gt",print_output=True)
    print(f"Verification {'succeeded' if result else 'failed'}")

    if not result:
        print("Feedback:", feedback)
##