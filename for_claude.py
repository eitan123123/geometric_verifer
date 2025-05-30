from z3 import *
import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple
from enum import Enum
from typing import Tuple, Optional
from fractions import Fraction
import logging

CONSTRUCTION_CDL = 'CONSTRUCTION_CDL'
TEXT_CDL = 'TEXT_CDL'
GOAL_CDL = 'GOAL_CDL'
CONSTRUCTION_CDL_EXTENDED = 'CONSTRUCTION_CDL_EXTENDED'
THEOREM_SEQUENCE = 'THEOREM_SEQUENCE'
ANSWER = 'ANSWER'
VERIFICATION_FAILED = "verification failed.\n\n"
PLEASE_FIX_PROOF = "\nPlease fix the proof."

# Goal description constants
GOAL_ANGLE = "- Goal: measure of angle {0}\n"
GOAL_LENGTH = "- Goal: length of line {0}\n"
GOAL_ARC_MEASURE = "- Goal: measure of arc {0}\n"
GOAL_RADIUS = "- Goal: radius of circle {0}\n"
GOAL_ARC_LENGTH = "- Goal: length of arc {0}\n"
GOAL_COSINE = "- Goal: cosine of angle {0}\n"
GOAL_SINE = "- Goal: sine of angle {0}\n"
GOAL_SUM = "- Goal: sum of lines {0} + {1}\n"
GOAL_RADIUS = "- Goal: radius of circle {0}\n"
GOAL_RATIO = "- Goal: ratio of lines {0} / {1}\n"
GOAL_PERIMETER = "- Goal: perimeter of triangle {0}\n"
GOAL_QUAD_AREA = "- Goal: area of quadrilateral {0}\n"
GOAL_GENERAL = "- Goal: value of {0}\n"
GOAL_DEFAULT = "- Goal: {0} {1}\n"

# Model answer and verifier expected answer
MODEL_ANSWER = "- Model answer: {0}\n"
VERIFIER_EXPECTED = "- Verifier expected answer: {0}\n"

# Error message headers
ERROR_HEADER = "- Error: "

# Error message constants
ERROR_UNSATISFIABLE = "Your proof contains contradictory constraints. Check for incorrect values in premises, improper theorem application, or conclusions that contradict earlier assertions.\n"
ERROR_INCOMPATIBLE = "From your proof, the verifier determines the {0} of {1} to be {2}, not {3} as you stated in your solution. Check your theorem applications and your answer.\n"
ERROR_MULTIPLE_VALUES = "Your proof doesn't uniquely determine the value. You need to use additional theorems to constrain the value.\n"
ERROR_INSUFFICIENT_INFO = "Your proof doesn't provide enough information to determine this value. You need to add theorems that specifically constrain {0} {1}.\n"
ERROR_CONTRADICTORY_CONSTRAINTS = "  Contradictory constraints:\n"
ERROR_CONSTRAINT_ITEM = "    {0}\n"

# Section headers
PREMISES_HEADER = "- Available premises:\n"
NO_GEOMETRIC_FACTS = "  No relevant geometric facts found.\n"
THEOREMS_HEADER = "- Theorems related to the goal:\n"
NO_RELATED_THEOREMS = "  None found that constrain this goal\n"
CONSTRAINTS_HEADER = "- Solver constraints directly related to this goal:\n"
NO_CONSTRAINTS = "  None found\n"
THEOREM_STEP_FORMAT = "  Step {0} - {1}({2}): {3}\n"


# Constants for premise error messages
TRIED_THEOREM = "You tried to use theorem: {0}({1});{2};{3}\n"
MISSING_PREMISE = "Missing premise: {0}\n"
DETAILS_PREFIX = "Details: {0}\n"

# Constants for trig function evaluation
TRIG_UNIQUE_VALUE = "{0}({1}) has a unique value: {2}"
CONTRADICTION_DETECTED = "Contradiction detected in evaluate_trig_function: {0}"
CALCULATED_FROM_ANGLE = "Calculated {0}({1}) = {2} from angle = {3}°"
CALCULATED_FROM_ALT_TRIG = "Calculated {0}({1}) = {2} from {3}({1}) = {4} (angle = {5}°)"
RELATED_CONSTRAINTS = "Related constraints for {0}({1}):"
CONSTRAINT_PREFIX = "  {0}"
NO_SPECIFIC_CONSTRAINTS = "No specific constraints found for {0}({1})"
NO_ANGLE_CONSTRAINTS = "No constraints found for angle {0} - insufficient information"
ANGLE_NOT_UNIQUE = "Angle {0} is not uniquely determined"
INVALID_SIN_VALUE = "Error: Invalid sin value {0} (exceeds 1)"
INVALID_COS_VALUE = "Error: Invalid cos value {0} (exceeds 1)"
ERROR_EVALUATING_ANGLE = "Error evaluating angle {0}: {1}"
ERROR_EVALUATING_TRIG = "Error evaluating {0} variable: {1}"
ERROR_CALCULATING_ALT_TRIG = "Error calculating from alternate trig function: {0}"

class ErrorTier(Enum):
    TIER1_THEOREM_CALL_SYNTAX_VIOLATION = 1  # Incorrect theorem call
    TIER2_PREMISE_VIOLATION = 2  # Premise violation
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
        self.defined_lines = set()
        self.mirror_congruent_triangles = []


        self.triangle_areas = {}
        self.altitude_facts = set()
        self.trapezoids = set()
        self.altitudes = {}
        self.quad_areas = {}
        self.quad_heights = {}
        self.quadrilateral_perimeters = {}
        # For handling both algebraic and numeric expressions
        self.variables = {}
        self.found_tier_1_or_2_error = False
        self.congruent_triangles = []
        self.mirror_congruent_triangles = []
        self.midsegments = set()
        self.equilateral_triangles = set()

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

        self.midsegments_of_quadrilaterals = {}
        # 3) We’ll also store any 'Cocircular(...)' facts, if needed
        self.cocircular_facts = []  # e.g. [("D", "B", "C", "A")] means D,B,C,A are on the same circle.

        # 4) For triangle area, we’ll keep a dictionary from triangle name to a Z3 Real for its area
        self.triangle_areas = {}

        # 5) We'll treat pi as a RealVal for approximate numeric checks
        from z3 import Const, RealVal, RealSort

        self.proven_area_relationships = []

        self.added_basic_constraints = set()

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
            self.solver.add(self.lengths[length_name] > 0)
        return self.lengths[length_name]

    def create_feedback_report(self, goal_type, goal_token, model_answer, verifier_expected_answer=None,
                               status="multiple_values", additional_info=None, error_message=None,
                               related_theorems=None, relevant_constraints=None, geometric_data=None):
        """
        Create a standardized feedback report that can be used by various feedback functions.

        Parameters:
        - goal_type: Type of the goal (angle, length, arc_measure, variable, etc.)
        - goal_token: The specific token for the goal (e.g., "ABC" for an angle)
        - model_answer: The user's proposed answer
        - verifier_expected_answer: The answer computed by the verifier (if available)
        - status: Status of the verification ("unsatisfiable", "incompatible", "multiple_values", "insufficient_info")
        - additional_info: Any additional information to include
        - error_message: Custom error message (if provided)
        - related_theorems: List of theorems related to the goal
        - relevant_constraints: List of constraints relevant to the goal
        - geometric_data: Dictionary of geometric facts categorized by type

        Returns:
        - A formatted feedback report string
        """

        # Initialize the report
        report = VERIFICATION_FAILED

        # Format goal description based on type
        if goal_type != "premise_error":
            if goal_type == "angle":
                report += GOAL_ANGLE.format(goal_token)
            elif goal_type == "length":
                report += GOAL_LENGTH.format(goal_token)
            elif goal_type == "arc_measure":
                report += GOAL_ARC_MEASURE.format(goal_token)
            elif goal_type == "arc_length":
                report += GOAL_ARC_LENGTH.format(goal_token)
            elif goal_type == "cosine":
                report += GOAL_COSINE.format(goal_token)
            elif goal_type == "sine":
                report += GOAL_SINE.format(goal_token)
            elif goal_type == "sum":
                tokens = goal_token.split('+')
                report += GOAL_SUM.format(tokens[0], tokens[1])
            elif goal_type == "ratio":
                tokens = goal_token.split('/')
                report += GOAL_RATIO.format(tokens[0], tokens[1])
            elif goal_type == "perimeter":
                report += GOAL_PERIMETER.format(goal_token)
            elif goal_type == "quad_area":
                report += GOAL_QUAD_AREA.format(goal_token)
            elif goal_type == "radius":
                report += GOAL_RADIUS.format(goal_token)
            elif goal_type == "general":
                report += GOAL_GENERAL.format(goal_token)
            else:
                report += GOAL_DEFAULT.format(goal_type, goal_token)

        # Add user's answer and expected/computed value if available
        if model_answer is not None:
            report += MODEL_ANSWER.format(model_answer)

        if verifier_expected_answer is not None and status == "incompatible":
            report += VERIFIER_EXPECTED.format(verifier_expected_answer)

        # Add error message
        report += ERROR_HEADER
        if error_message:
            report += error_message
        else:
            if status == "unsatisfiable":
                report += ERROR_UNSATISFIABLE

                # Add information about contradictory constraints if available
                contradictory_constraints = self.find_contradictory_constraints()
                if contradictory_constraints:
                    report += ERROR_CONTRADICTORY_CONSTRAINTS
                    for constraint in contradictory_constraints:
                        report += ERROR_CONSTRAINT_ITEM.format(constraint)
            elif status == "incompatible":
                report += ERROR_INCOMPATIBLE.format(goal_type, goal_token, verifier_expected_answer, model_answer)
            elif status == "multiple_values":
                report += ERROR_MULTIPLE_VALUES
            elif status == "insufficient_info":
                report += ERROR_INSUFFICIENT_INFO.format(goal_type, goal_token)

        # Add all geometric facts for context
        report += PREMISES_HEADER

        if not geometric_data:
            geometric_data = self.gather_relevant_geometric_data(
                goal_variable=goal_token if goal_type == "general" else None
            )

        # Define patterns to clean up different fact categories
        category_patterns = {
            "Cocircular Points": [("Points ", "")],
            "Polygons": [("Polygon ", "")],
            "Collinear Points": [("Collinear ", "")],
            "Parallel Lines": [("Line ", "")],
            "Perpendicular Lines": [("Line ", "")],
            "Right Triangles": [("Right triangle ", "")],
            "Similar Triangles": [(" similar to ", " ~ ")],
            "Congruent Triangles": [(" congruent to ", " ≅ ")],
            "Circles": [("Circle ", ""), (" with center ", " center: ")],
            "Circle Diameters": [("Line ", ""), (" is diameter of circle ", " diameter of ")],
            "Tangent Lines": [("Line ", ""), (" is tangent to circle ", " tangent to ")],
            "Squares": [("Square ", "")],
            "Rectangles": [("Rectangle ", "")],
            "Rhombi": [("Rhombus ", "")],
            "Kites": [("Kite ", "")]
        }

        if geometric_data:
            for category, facts in geometric_data.items():
                if facts:  # Only show categories with facts
                    report += f"  {category}: "
                    cleaned_facts = []

                    for fact in facts:
                        # Clean up each fact by removing redundant prefixes
                        cleaned_fact = fact

                        # Apply all replacements for this category
                        if category in category_patterns:
                            for pattern, replacement in category_patterns[category]:
                                cleaned_fact = cleaned_fact.replace(pattern, replacement)

                        cleaned_facts.append(cleaned_fact)

                    # Join all facts with commas and add a newline at the end
                    report += f"{', '.join(cleaned_facts)}\n"
        else:
            report += NO_GEOMETRIC_FACTS

        # Add theorems related to the goal if provided
        report += THEOREMS_HEADER

        if related_theorems:
            for theorem in related_theorems:
                report += THEOREM_STEP_FORMAT.format(
                    theorem['step'],
                    theorem['theorem'],
                    ', '.join(theorem['args']),
                    theorem['conclusion']
                )
        else:
            report += NO_RELATED_THEOREMS

        # Add solver constraints
        report += CONSTRAINTS_HEADER

        if relevant_constraints:
            # Convert to list if it's a set
            if isinstance(relevant_constraints, set):
                relevant_constraints = list(relevant_constraints)

            # Sort for consistent output
            try:
                relevant_constraints.sort()
            except:
                pass  # Continue if sorting fails

            for constraint in relevant_constraints:
                report += f"  {constraint}\n"
        else:
            report += NO_CONSTRAINTS

        # Add additional information if provided
        if additional_info:
            report += f"\n{additional_info}"

        # Final message
        report += PLEASE_FIX_PROOF

        return report




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

    def canonicalize_mirror_congruent_triangle_pair(self, tri1: str, tri2: str) -> Tuple[str, str]:
        """
        Normalize triangles for mirror congruence checking.
        For mirror congruent triangles, we consider rotations only.
        """
        # For first triangle, generate all rotations
        rotations1 = [tri1[i:] + tri1[:i] for i in range(len(tri1))]

        # For second triangle, generate all rotations
        rotations2 = [tri2[i:] + tri2[:i] for i in range(len(tri2))]

        # Find the lexicographically smallest pair
        canonical_pair = min((r1, r2) for r1 in rotations1 for r2 in rotations2)

        return canonical_pair

    def find_contradictory_constraints(self, max_constraints=10):
        """
        Find a small subset of constraints that are contradictory using Z3's unsat core feature.

        Args:
            max_constraints: Maximum number of constraints to return

        Returns:
            list: A list of formatted contradictory constraints
        """
        from z3 import Solver, unsat, Bool

        # Get all assertions from the current solver
        assertions = list(self.solver.assertions())

        # Create a new solver for unsat core tracking
        core_solver = Solver()
        tracking = {}

        # Add each assertion with a tracking variable
        for i, a in enumerate(assertions):
            a_str = str(a)

            # Skip pi constant definitions and basic bounds constraints
            if any(x in a_str for x in ["pi ==", "angle_ > 0", "angle_ <= 180", "length_ > 0",
                                        "arc_ >= 0", "arc_ <= 360", ">= -1", "<= 1"]):
                continue

            # Create a tracking variable
            track_var = Bool(f"track_{i}")
            tracking[track_var] = a
            core_solver.assert_and_track(a, track_var)

        # Check if still unsat and get the core
        if core_solver.check() == unsat:
            core = core_solver.unsat_core()

            # Convert core to original assertions
            contradiction = []
            for var in core:
                if var in tracking:
                    constraint = self.format_constraint(str(tracking[var]))
                    if constraint not in contradiction:
                        contradiction.append(constraint)

            # Limit the number of constraints returned
            return contradiction[:max_constraints]

        return []  # If not unsatisfiable with the filtered set



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

    def collect_variable_references(self, variable_name, max_constraints=50):
        """
        Collect all references to a specific variable in the proof using a generalized approach.

        Args:
            variable_name (str): The name of the variable to search for (e.g., 'p')
            max_constraints (int): Maximum number of constraints to collect

        Returns:
            dict: A dictionary containing different types of references to the variable
        """
        references = {
            "angle_expressions": [],  # Expressions like MeasureOfAngle(ABC) = 3*p+5
            "length_expressions": [],  # Expressions like LengthOfLine(AB) = 2*p
            "arc_expressions": [],  # Expressions like MeasureOfArc(ABC) = p+10
            "algebraic_constraints": [],  # Direct algebraic constraints like p = 25
            "solver_constraints": [],  # Z3 solver constraints involving p
            "related_constraints": [],  # Related constraints between variables
            "related_theorems": []  # Theorems that establish values related to p
        }

        # Regular expression to match the variable as a standalone identifier
        var_pattern = re.compile(r'(^|[^a-zA-Z0-9_])' + re.escape(variable_name) + r'([^a-zA-Z0-9_]|$)')

        # 1. Search TEXT_CDL section if available
        if hasattr(self, 'text_cdl_lines'):
            for line in self.text_cdl_lines:
                # Look for angle expressions containing the variable
                angle_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                if angle_match and var_pattern.search(angle_match.group(2)):
                    angle_name, expr = angle_match.groups()
                    references["angle_expressions"].append(f"∠{angle_name} = {expr.strip()}")

                # Look for length expressions containing the variable
                length_match = re.search(r'Equal\(LengthOfLine\((\w+)\),(.*?)\)', line)
                if length_match and var_pattern.search(length_match.group(2)):
                    line_name, expr = length_match.groups()
                    references["length_expressions"].append(f"|{line_name}| = {expr.strip()}")

                # Look for arc expressions containing the variable
                arc_match = re.search(r'Equal\(MeasureOfArc\((\w+)\),(.*?)\)', line)
                if arc_match and var_pattern.search(arc_match.group(2)):
                    arc_name, expr = arc_match.groups()
                    references["arc_expressions"].append(f"arc {arc_name} = {expr.strip()}")

                # Look for direct algebraic constraints on the variable
                direct_match = re.search(rf'Equal\({variable_name},(.*?)\)', line)
                if direct_match:
                    references["algebraic_constraints"].append(f"{variable_name} = {direct_match.group(1).strip()}")
                elif re.search(rf'{variable_name}\s*=', line):
                    references["algebraic_constraints"].append(line.strip())

        # 2. Use our new generalized constraint finder
        try:
            relevant_constraints = self.find_relevant_constraints(variable_name)
            references["solver_constraints"] = relevant_constraints["direct_constraints"]
            references["related_constraints"] = relevant_constraints["related_constraints"]
        except Exception as e:
            print(f"Error finding constraints: {e}")
            # If general approach fails, provide a simple fallback
            for c in self.solver.assertions():
                c_str = str(c)
                if var_pattern.search(c_str) and "pi ==" not in c_str:
                    references["solver_constraints"].append(self.format_constraint(c_str))

        # 3. Check theorem sequence for conclusions involving the variable
        for theorem_info in self.theorem_sequence:
            for conclusion in theorem_info["conclusions"]:
                if var_pattern.search(conclusion):
                    references["related_theorems"].append({
                        "step": theorem_info["step_number"],
                        "theorem": theorem_info["theorem_name"],
                        "args": theorem_info["args"],
                        "conclusion": conclusion
                    })
                    break  # Only add each theorem once

            # Also check premises for the variable
            if var_pattern.search(theorem_info["premise"]):
                # Add this as a related theorem since the variable appears in the premise
                if not any(t["step"] == theorem_info["step_number"] for t in references["related_theorems"]):
                    references["related_theorems"].append({
                        "step": theorem_info["step_number"],
                        "theorem": theorem_info["theorem_name"],
                        "args": theorem_info["args"],
                        "conclusion": "Variable in premise: " + theorem_info["premise"]
                    })

        return references

    def get_direct_variable_constraints(self, variable_name):
        """
        A simpler, more efficient approach to get just the algebraic constraints on a variable.
        This should be fast even with many angles and assertions.
        """
        constraints = []

        # Regular expression to match the variable as a standalone identifier
        var_pattern = re.compile(r'(^|[^a-zA-Z0-9_])' + re.escape(variable_name) + r'([^a-zA-Z0-9_]|$)')

        # 1. Check TEXT_CDL for direct expressions with the variable
        if hasattr(self, 'text_cdl_lines'):
            for line in self.text_cdl_lines:
                if var_pattern.search(line):
                    # Angle expressions
                    angle_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                    if angle_match and var_pattern.search(angle_match.group(2)):
                        angle_name, expr = angle_match.groups()
                        constraints.append(f"∠{angle_name} = {expr.strip()}")
                        continue

                    # Length expressions
                    length_match = re.search(r'Equal\(LengthOfLine\((\w+)\),(.*?)\)', line)
                    if length_match and var_pattern.search(length_match.group(2)):
                        line_name, expr = length_match.groups()
                        constraints.append(f"|{line_name}| = {expr.strip()}")
                        continue

                    # Direct variable assignments
                    direct_match = re.search(rf'Equal\({variable_name},(.*?)\)', line)
                    if direct_match:
                        constraints.append(f"{variable_name} = {direct_match.group(1).strip()}")
                        continue

                    # Basic assignment (variable = value)
                    simple_match = re.search(rf'{variable_name}\s*=\s*(.*?)(?:$|[,);])', line)
                    if simple_match:
                        constraints.append(f"{variable_name} = {simple_match.group(1).strip()}")
                        continue

        # 2. For the theorem sequence, just show theorems that establish equations with the variable
        for theorem_info in self.theorem_sequence:
            for conclusion in theorem_info["conclusions"]:
                if "Equal" in conclusion and var_pattern.search(conclusion):
                    constraints.append(
                        f"Step {theorem_info['step_number']} - {theorem_info['theorem_name']} establishes: {conclusion}"
                    )
                    break

        return constraints

    def format_constraint(self, constraint_str):
        """
        Format a Z3 constraint string to be more readable.

        Args:
            constraint_str (str): The original constraint string from Z3

        Returns:
            str: A more readable formatted constraint
        """
        # Skip if this is a comment or special marker
        if constraint_str.startswith('#'):
            return constraint_str

        # Remove leading "0 + " that commonly appears in sum expressions
        constraint_str = re.sub(r'^0\s*\+\s*', '', constraint_str)

        # Replace angle_ABC with ∠ABC for better readability, but be careful of word boundaries
        constraint_str = re.sub(r'(^|[^a-zA-Z0-9_])angle_(\w+)', r'\1∠\2', constraint_str)

        # Replace length_AB with |AB| for better readability
        constraint_str = re.sub(r'(^|[^a-zA-Z0-9_])length_(\w+)', r'\1|\2|', constraint_str)

        # Replace arc_ABC with arc(ABC) for better readability
        constraint_str = re.sub(r'(^|[^a-zA-Z0-9_])arc_(\w+)', r'\1arc(\2)', constraint_str)

        # Replace common Z3 operators
        constraint_str = constraint_str.replace(' == ', ' = ')
        constraint_str = constraint_str.replace(' + ', ' + ')
        constraint_str = constraint_str.replace(' - ', ' - ')
        constraint_str = constraint_str.replace(' * ', ' × ')
        constraint_str = constraint_str.replace(' / ', ' ÷ ')

        # Remove leading/trailing spaces
        constraint_str = constraint_str.strip()

        return constraint_str




    def gather_relevant_geometric_data(self, excluded_categories=None, goal_variable=None):
        """
        Collect all non-empty geometric facts that might be relevant for feedback.

        Args:
            excluded_categories: List of category names to exclude from the output
            goal_variable: If specified, filter facts to only show those relevant to this variable
        """
        if excluded_categories is None:
            excluded_categories = []  # Don't exclude any categories by default

        geometric_data = {}

        # Get related angles and lengths if goal_variable is provided
        related_points = set()
        if goal_variable and hasattr(self, 'text_cdl_lines'):
            for line in self.text_cdl_lines:
                if goal_variable in line:
                    # Extract angle points related to goal variable
                    angle_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                    if angle_match and goal_variable in angle_match.group(2):
                        angle_points = angle_match.group(1)
                        for point in angle_points:
                            related_points.add(point)

                    # Extract length points related to goal variable
                    length_match = re.search(r'Equal\(LengthOfLine\((\w+)\),(.*?)\)', line)
                    if length_match and goal_variable in length_match.group(2):
                        length_points = length_match.group(1)
                        for point in length_points:
                            related_points.add(point)

        # Parallel lines - with proper deduplication
        if self.parallel_pairs:
            formatted_pairs = set()
            for p1, p2 in self.parallel_pairs:
                # Normalize each line by sorting characters within the line
                line1 = ''.join(sorted(p1))
                line2 = ''.join(sorted(p2))

                # Normalize the pair by sorting the normalized lines
                sorted_pair = tuple(sorted([line1, line2]))
                formatted_pairs.add(f"{sorted_pair[0]} ∥ {sorted_pair[1]}")

            if formatted_pairs and "Parallel Lines" not in excluded_categories:
                geometric_data["Parallel Lines"] = sorted(formatted_pairs)

        # Perpendicular lines - with proper deduplication
        if self.perpendicular_pairs:
            formatted_pairs = set()
            for p1, p2 in self.perpendicular_pairs:
                # Normalize each line by sorting characters within the line
                line1 = ''.join(sorted(p1))
                line2 = ''.join(sorted(p2))

                # Normalize the pair by sorting the normalized lines
                sorted_pair = tuple(sorted([line1, line2]))
                formatted_pairs.add(f"{sorted_pair[0]} ⊥ {sorted_pair[1]}")

            if formatted_pairs and "Perpendicular Lines" not in excluded_categories:
                geometric_data["Perpendicular Lines"] = sorted(formatted_pairs)

        # Collinear facts - filter by relevant points if goal_variable provided
        if self.collinear_facts and "Collinear Points" not in excluded_categories:
            filtered_facts = []

            for points in self.collinear_facts:
                # If we have a goal variable, only include collinear facts containing related points
                if goal_variable and related_points:
                    if any(p in related_points for p in points):
                        filtered_facts.append(f"Collinear {''.join(points)}")
                else:
                    # Otherwise include all collinear facts
                    filtered_facts.append(f"Collinear {''.join(points)}")

            if filtered_facts:
                geometric_data["Collinear Points"] = sorted(set(filtered_facts))

        # Right triangles
        if self.right_triangles and "Right Triangles" not in excluded_categories:
            formatted_triangles = [f"Right triangle {tri}" for tri in self.right_triangles]
            if formatted_triangles:
                geometric_data["Right Triangles"] = sorted(set(formatted_triangles))

        # Similar triangles
        if self.similar_triangles and "Similar Triangles" not in excluded_categories:
            formatted_pairs = [f"{tri1} similar to {tri2}" for tri1, tri2 in self.similar_triangles]
            if formatted_pairs:
                geometric_data["Similar Triangles"] = sorted(set(formatted_pairs))

        # Congruent triangles
        if hasattr(self,
                   'congruent_triangles') and self.congruent_triangles and "Congruent Triangles" not in excluded_categories:
            formatted_pairs = [f"{tri1} congruent to {tri2}" for tri1, tri2 in self.congruent_triangles]
            if formatted_pairs:
                geometric_data["Congruent Triangles"] = sorted(set(formatted_pairs))

        # Mirror Congruent triangles
        if hasattr(self,
                   'mirror_congruent_triangles') and self.mirror_congruent_triangles and "Mirror Congruent Triangles" not in excluded_categories:
            formatted_pairs = [f"{tri1} mirror congruent to {tri2}" for tri1, tri2 in self.mirror_congruent_triangles]
            if formatted_pairs:
                geometric_data["Mirror Congruent Triangles"] = sorted(set(formatted_pairs))

        # Mirror Similar triangles
        if hasattr(self,
                   'mirror_similar_triangles') and self.mirror_similar_triangles and "Mirror Similar Triangles" not in excluded_categories:
            formatted_pairs = [f"{tri1} mirror similar to {tri2}" for tri1, tri2 in self.mirror_similar_triangles]
            if formatted_pairs:
                geometric_data["Mirror Similar Triangles"] = sorted(set(formatted_pairs))

        # Cocircular facts
        if hasattr(self,
                   'cocircular_facts') and self.cocircular_facts and "Cocircular Points" not in excluded_categories:
            formatted_cocircular = []
            for fact in self.cocircular_facts:
                if fact and len(fact) > 1:
                    circle = fact[0]
                    points = ''.join(fact[1:])
                    formatted_cocircular.append(f"Points {points} on circle {circle}")
            if formatted_cocircular:
                geometric_data["Cocircular Points"] = sorted(set(formatted_cocircular))

        # Circles
        if hasattr(self, 'circle_centers') and self.circle_centers and "Circles" not in excluded_categories:
            formatted_centers = [f"Circle {circle} with center {center}" for circle, center in
                                 self.circle_centers.items()]
            if formatted_centers:
                geometric_data["Circles"] = sorted(set(formatted_centers))

        # Circle diameters
        if hasattr(self,
                   'is_diameter_of_circle') and self.is_diameter_of_circle and "Circle Diameters" not in excluded_categories:
            formatted_diameters = [f"Line {line} is diameter of circle {circle}" for line, circle in
                                   self.is_diameter_of_circle]
            if formatted_diameters:
                geometric_data["Circle Diameters"] = sorted(set(formatted_diameters))

        # Tangent facts
        if hasattr(self, 'tangent_facts') and self.tangent_facts and "Tangent Lines" not in excluded_categories:
            formatted_tangents = [f"Line {line} is tangent to circle {circle}" for line, circle in self.tangent_facts]
            if formatted_tangents:
                geometric_data["Tangent Lines"] = sorted(set(formatted_tangents))

        # Squares
        if hasattr(self, 'squares') and self.squares and "Squares" not in excluded_categories:
            formatted_squares = [f"Square {square}" for square in self.squares]
            if formatted_squares:
                geometric_data["Squares"] = sorted(set(formatted_squares))

        # Rectangles
        if hasattr(self, 'rectangles') and self.rectangles and "Rectangles" not in excluded_categories:
            formatted_rectangles = [f"Rectangle {rect}" for rect in self.rectangles]
            if formatted_rectangles:
                geometric_data["Rectangles"] = sorted(set(formatted_rectangles))

        # Rhombi
        if hasattr(self, 'rhombi') and self.rhombi and "Rhombi" not in excluded_categories:
            formatted_rhombi = [f"Rhombus {rhom}" for rhom in self.rhombi]
            if formatted_rhombi:
                geometric_data["Rhombi"] = sorted(set(formatted_rhombi))

        # Kites
        if hasattr(self, 'kites') and self.kites and "Kites" not in excluded_categories:
            formatted_kites = [f"Kite {kite}" for kite in self.kites]
            if formatted_kites:
                geometric_data["Kites"] = sorted(set(formatted_kites))

        # Polygons
        if self.polygons and "Polygons" not in excluded_categories:
            formatted_polygons = [f"Polygon {poly}" for poly in self.polygons]
            if formatted_polygons:
                geometric_data["Polygons"] = sorted(set(formatted_polygons))

        # Remove empty categories
        return {k: v for k, v in geometric_data.items() if v}

    def evaluate_trig_function(self, func_name, angle_token, model_answer):
        """
        Evaluates a trigonometric function (sin/cos) for an angle.
        Provides better error handling and feedback for contradictions.

        Args:
            func_name: Either "sin" or "cos"
            angle_token: The angle name (e.g., "BAC")
            model_answer: The expected answer to verify

        Returns:
            tuple of (success, value, status)
        """
        import math
        epsilon = 1e-8  # Common epsilon value for all goals

        # First, try to get the angle variable directly
        angle_var = self.add_angle(angle_token[0], angle_token[1], angle_token[2])

        # Create or get the trig function variable if it exists
        trig_var_name = f"{func_name}_{angle_token}"
        if trig_var_name not in self.variables:
            self.variables[trig_var_name] = Real(trig_var_name)
            # Add bounds for sine/cosine
            self.solver.add(self.variables[trig_var_name] >= -1)
            self.solver.add(self.variables[trig_var_name] <= 1)

        trig_var = self.variables[trig_var_name]

        # Check if the system is satisfiable
        check_result = self.solver.check()

        if check_result == unsat:
            # System is unsatisfiable - there's a contradiction
            contradictory_constraints = self.find_contradictory_constraints()
            details = "No specific contradictory constraints found."

            if contradictory_constraints:
                details = ERROR_CONTRADICTORY_CONSTRAINTS
                for constraint in contradictory_constraints:
                    details += ERROR_CONSTRAINT_ITEM.format(constraint)

            print(CONTRADICTION_DETECTED.format(details))
            return False, None, "unsatisfiable"

        elif check_result == sat:
            model = self.solver.model()

            # First approach: Check if the trig function variable already has a value
            try:
                trig_val_str = model.eval(trig_var).as_decimal(10)
                if trig_val_str.endswith('?'):
                    trig_val_str = trig_val_str[:-1]
                trig_val = float(trig_val_str)

                # Check if this value is uniquely determined
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                temp_solver.add(Or(trig_var < trig_val - epsilon, trig_var > trig_val + epsilon))

                if temp_solver.check() == unsat:
                    # Value is uniquely determined
                    print(TRIG_UNIQUE_VALUE.format(func_name, angle_token, trig_val))
                    if abs(trig_val - model_answer) < epsilon:
                        return True, trig_val, "unique"
                    else:
                        return False, trig_val, "incompatible"
            except Exception as e:
                print(ERROR_EVALUATING_TRIG.format(func_name, e))

            # Second approach: Try to calculate from the angle if it exists
            try:
                angle_val_str = model.eval(angle_var).as_decimal(10)
                if angle_val_str.endswith('?'):
                    angle_val_str = angle_val_str[:-1]
                angle_val = float(angle_val_str)

                # Check if angle is uniquely determined
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                temp_solver.add(Or(angle_var < angle_val - epsilon, angle_var > angle_val + epsilon))

                if temp_solver.check() == unsat:
                    # Angle is uniquely determined, calculate trig function
                    if func_name == "sin":
                        calculated_val = math.sin(math.radians(angle_val))
                    else:  # cos
                        calculated_val = math.cos(math.radians(angle_val))

                    print(CALCULATED_FROM_ANGLE.format(func_name, angle_token, calculated_val, angle_val))

                    if abs(calculated_val - model_answer) < epsilon:
                        return True, calculated_val, "unique"
                    else:
                        return False, calculated_val, "incompatible"
                else:
                    print(ANGLE_NOT_UNIQUE.format(angle_token))
            except Exception as e:
                print(ERROR_EVALUATING_ANGLE.format(angle_token, e))

            # Third approach: Try to calculate from the alternate trig function
            alt_func_name = "cos" if func_name == "sin" else "sin"
            alt_trig_var_name = f"{alt_func_name}_{angle_token}"

            if alt_trig_var_name in self.variables:
                alt_trig_var = self.variables[alt_trig_var_name]

                try:
                    # Get the alternate trig value from the model
                    alt_trig_val_str = model.eval(alt_trig_var).as_decimal(10)
                    if alt_trig_val_str.endswith('?'):
                        alt_trig_val_str = alt_trig_val_str[:-1]
                    alt_trig_val = float(alt_trig_val_str)

                    # Check if the alternate trig value is uniquely determined
                    temp_solver = Solver()
                    for c in self.solver.assertions():
                        temp_solver.add(c)

                    temp_solver.add(Or(alt_trig_var < alt_trig_val - epsilon, alt_trig_var > alt_trig_val + epsilon))

                    if temp_solver.check() == unsat:
                        # Alternate trig value is uniquely determined
                        # Calculate the angle from the alternate trig function
                        import math

                        # Get the angle (in degrees) from the alternate trig function
                        if alt_func_name == "sin":
                            # If we have sin, use arcsin
                            if abs(alt_trig_val) > 1:
                                print(INVALID_SIN_VALUE.format(alt_trig_val))
                                return False, None, "multiple_values"
                            angle_in_degrees = math.degrees(math.asin(alt_trig_val))
                        else:  # alt_func_name == "cos"
                            # If we have cos, use arccos
                            if abs(alt_trig_val) > 1:
                                print(INVALID_COS_VALUE.format(alt_trig_val))
                                return False, None, "multiple_values"
                            angle_in_degrees = math.degrees(math.acos(alt_trig_val))

                        # Handle multiple possible angles (arcsin/arccos can have multiple solutions)
                        possible_angles = [angle_in_degrees]
                        if alt_func_name == "sin":
                            # If sin(θ) = k, then sin(180-θ) = k as well
                            possible_angles.append(180 - angle_in_degrees)
                        else:  # alt_func_name == "cos"
                            # If cos(θ) = k, then cos(360-θ) = k as well
                            possible_angles.append(360 - angle_in_degrees)

                        # Try each possible angle
                        for angle_val in possible_angles:
                            # Calculate the requested trig function using the determined angle
                            if func_name == "sin":
                                calculated_val = math.sin(math.radians(angle_val))
                            else:  # func_name == "cos"
                                calculated_val = math.cos(math.radians(angle_val))

                            print(CALCULATED_FROM_ALT_TRIG.format(
                                func_name, angle_token, calculated_val, alt_func_name, alt_trig_val, angle_val
                            ))

                            # Check if this calculated value matches the expected answer
                            if abs(calculated_val - model_answer) < epsilon:
                                return True, calculated_val, "unique"

                        # If we get here, none of the calculated values matched
                        return False, calculated_val, "incompatible"

                except Exception as e:
                    print(ERROR_CALCULATING_ALT_TRIG.format(e))

            # Provide better feedback on why it's not uniquely determined
            related_constraints = []
            for c in self.solver.assertions():
                c_str = str(c)
                if f"{func_name}_{angle_token}" in c_str or f"angle_{angle_token}" in c_str:
                    related_constraints.append(self.format_constraint(c_str))

            if related_constraints:
                print(RELATED_CONSTRAINTS.format(func_name, angle_token))
                for constraint in related_constraints:
                    print(CONSTRAINT_PREFIX.format(constraint))
            else:
                print(NO_SPECIFIC_CONSTRAINTS.format(func_name, angle_token))

            # Check if we have any constraints on the angle at all
            angle_constraints = []
            for c in self.solver.assertions():
                c_str = str(c)
                if f"angle_{angle_token}" in c_str:
                    angle_constraints.append(self.format_constraint(c_str))

            if not angle_constraints:
                print(NO_ANGLE_CONSTRAINTS.format(angle_token))
                return False, None, "insufficient_info"

            # If we get here, we couldn't determine the value from any method
            return False, None, "multiple_values"
        else:
            return False, None, "unknown"

    def normalize_quadrilateral(self, quad_name: str) -> str:
        """
        Normalize a quadrilateral name to handle different permutations.
        For a quadrilateral, we find all cyclic permutations and return the
        lexicographically smallest one.
        """
        # Get all cyclic permutations
        permutations = []
        n = len(quad_name)
        for i in range(n):
            permutation = quad_name[i:] + quad_name[:i]
            permutations.append(permutation)

        # Return the lexicographically smallest permutation
        return min(permutations)

    def is_midsegment_of_quadrilateral(self, segment: str, quad: str) -> bool:
        """
        Check if the given segment is stored as a midsegment of the given quadrilateral.
        This handles normalization of the quadrilateral name.
        """
        # Normalize quadrilateral name
        norm_quad = self.normalize_quadrilateral(quad)

        # Check all permutations of the segment (FE vs EF)
        segments = [segment, segment[::-1]]

        # Check if any combination exists in our stored midsegments
        for seg in segments:
            if (seg, norm_quad) in self.midsegments_of_quadrilaterals:
                return True

        return False

    def identify_midsegment_quadrilateral(self, segment: str, quad: str) -> bool:
        """
        Check if a segment can be identified as a midsegment of a quadrilateral
        by analyzing if it connects midpoints of opposite sides.
        """
        if len(segment) != 2 or len(quad) != 4:
            return False

        # Check if we have midpoint information about the segment endpoints
        e_midpoint_of = []
        f_midpoint_of = []

        # Use previously established midpoint information
        if hasattr(self, "midpoints"):
            for (p1, p2), midpoint in self.midpoints.items():
                if midpoint == segment[0]:  # First point of segment (e.g., "E")
                    e_midpoint_of.append((p1, p2))
                elif midpoint == segment[1]:  # Second point of segment (e.g., "F")
                    f_midpoint_of.append((p1, p2))

        # If we don't have enough midpoint information, return False
        if not e_midpoint_of or not f_midpoint_of:
            return False

        # Get the sides of the quadrilateral (in order)
        sides = [
            (quad[0], quad[1]),
            (quad[1], quad[2]),
            (quad[2], quad[3]),
            (quad[3], quad[0])
        ]

        # Convert sides to sets for easier comparison (AB == BA)
        sides_sets = [set(side) for side in sides]

        # Check if E and F are midpoints of opposite sides
        for e_side in e_midpoint_of:
            e_side_set = set(e_side)
            e_side_idx = -1

            # Find which side E is the midpoint of
            for i, side_set in enumerate(sides_sets):
                if e_side_set == side_set:
                    e_side_idx = i
                    break

            if e_side_idx == -1:
                continue

            # Check if F is the midpoint of the opposite side
            opposite_idx = (e_side_idx + 2) % 4
            opposite_side_set = sides_sets[opposite_idx]

            for f_side in f_midpoint_of:
                if set(f_side) == opposite_side_set:
                    return True

        return False

    def check_midsegment_with_permutations(self, segment: str, quad: str) -> bool:
        """
        Check if a segment is a midsegment of a quadrilateral considering all
        possible permutations of the quadrilateral.
        """
        # Check all cyclic permutations of the quadrilateral
        for i in range(len(quad)):
            perm = quad[i:] + quad[:i]

            # Check both segment orientations
            if self.is_midsegment_of_quadrilateral(segment, perm) or \
                    self.is_midsegment_of_quadrilateral(segment[::-1], perm):
                return True

            # Also try to identify it geometrically
            if self.identify_midsegment_quadrilateral(segment, perm) or \
                    self.identify_midsegment_quadrilateral(segment[::-1], perm):
                # If identified, store it for future reference
                norm_quad = self.normalize_quadrilateral(perm)
                self.midsegments_of_quadrilaterals[(segment, norm_quad)] = True
                self.midsegments_of_quadrilaterals[(segment[::-1], norm_quad)] = True
                return True

        return False

    def get_opposite_sides_of_quadrilateral(self, quad: str) -> list:
        """
        Get the pairs of opposite sides in a quadrilateral.
        """
        if len(quad) != 4:
            return []

        # For a quadrilateral with vertices in cyclic order A,B,C,D:
        # - Side 1: AB, Side 2: BC, Side 3: CD, Side 4: DA
        # - Opposite sides are: (AB, CD) and (BC, DA)
        sides = [
            (quad[0] + quad[1], quad[2] + quad[3]),  # Sides 1 and 3
            (quad[1] + quad[2], quad[3] + quad[0])  # Sides 2 and 4
        ]

        return sides

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

    def generate_detailed_feedback(self, goal_type, goal_token, model_answer, verifier_expected_answer=None,
                                   status="multiple_values", additional_info=None):
        """Generate feedback in the user's preferred format with improved content filtering."""

        # Find theorems directly related to the goal
        related_theorems = []

        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check for direct mention of the goal in conclusions
            for conclusion in theorem_info["conclusions"]:
                if goal_token in conclusion:
                    is_related = True
                    break

                # Check more carefully depending on goal type
                if not is_related and goal_type in ["angle", "arc_measure", "arc_length", "sine", "cosine"]:
                    for conclusion in theorem_info["conclusions"]:
                        pattern = rf'(MeasureOf(Angle|Arc)|Sin|Cos)\((\w+)\)'
                        matches = re.findall(pattern, conclusion)
                        for match in matches:
                            if match[1] == goal_token or set(match[1]) == set(goal_token):
                                is_related = True
                                break

            # Check if mentioned in the premise
            if goal_token in theorem_info["premise"]:
                is_related = True

            # Check if mentioned in args
            if any(goal_token in arg for arg in theorem_info["args"]):
                is_related = True

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        # Determine appropriate variable names based on goal type for constraints
        var_names = []
        if goal_type == "arc_length":
            var_names.append(f"lengthArc_{self.normalize_arc(goal_token)}")
            var_names.append(f"arc_{self.normalize_arc(goal_token)}")
        elif goal_type == "arc_measure":
            var_names.append(f"arc_{self.normalize_arc(goal_token)}")
        elif goal_type == "length":
            var_names.append(f"length_{self.normalize_line_name(goal_token)}")
        elif goal_type == "angle":
            var_names.append(f"angle_{self.normalize_angle_name(goal_token)}")
        elif goal_type == "cosine":
            var_names.append(f"cos_{goal_token}")
            var_names.append(f"angle_{self.normalize_angle_name(goal_token)}")
        elif goal_type == "sine":
            var_names.append(f"sin_{goal_token}")
            var_names.append(f"angle_{self.normalize_angle_name(goal_token)}")
        elif goal_type == "sum":
            tokens = goal_token.split('+')
            for token in tokens:
                var_names.append(f"length_{self.normalize_line_name(token)}")
        elif goal_type == "ratio":
            tokens = goal_token.split('/')
            for token in tokens:
                var_names.append(f"length_{self.normalize_line_name(token)}")
        elif goal_type == "perimeter":
            var_names.append(f"perimeter_{goal_token}")
        elif goal_type == "quad_area":
            var_names.append(f"AreaOfQuadrilateral_{goal_token}")

        # Use a set to track unique constraints
        unique_constraints = set()

        for c in self.solver.assertions():
            c_str = str(c)
            for var_name in var_names:
                if var_name in c_str:
                    # Format constraint for readability
                    formatted = self.format_constraint(c_str)
                    unique_constraints.add(formatted)
                    break

        # Convert to list and sort for consistent output
        relevant_constraints = sorted(list(unique_constraints))

        # Use the common feedback report function
        return self.create_feedback_report(
            goal_type=goal_type,
            goal_token=goal_token,
            model_answer=model_answer,
            verifier_expected_answer=verifier_expected_answer,
            status=status,
            additional_info=additional_info,
            related_theorems=related_theorems,
            relevant_constraints=relevant_constraints
        )

    # Second function: Update for variable goals specifically
    def generate_detailed_feedback_for_variable(self, variable_name, model_answer, verifier_expected_answer=None,
                                                status="multiple_values"):
        """Generate detailed feedback specifically for a variable goal with improved formatting."""

        # Get direct constraints for the variable
        direct_constraints = self.get_direct_variable_constraints(variable_name)

        # Get geometric facts filtered to show only those relevant to this variable
        geometric_data = self.gather_relevant_geometric_data(goal_variable=variable_name)

        # Get related theorems
        related_theorems = self.find_related_theorems_for_variable(variable_name)

        # Get solver constraints
        try:
            result = self.find_relevant_constraints(variable_name)
            # Add direct constraints first
            unique_constraints = set(result["direct_constraints"])
            # Then add related constraints
            for constraint in result["related_constraints"]:
                unique_constraints.add(constraint)

            # Convert to list and sort
            all_constraints = list(unique_constraints)

            def constraint_sort_key(constraint):
                priority = 0 if variable_name in constraint else 1
                return (priority, constraint)

            all_constraints.sort(key=constraint_sort_key)
        except Exception as e:
            print(f"Error finding constraints: {e}")
            all_constraints = [f"Error finding constraints: {e}"]

        # Add contradictory constraints if needed
        contradictory_constraints = None
        if status == "unsatisfiable":
            contradictory_constraints = self.find_contradictory_constraints()

        # Create custom error message for unsatisfiable case
        error_message = None
        if status == "unsatisfiable" and contradictory_constraints:
            error_message = ERROR_UNSATISFIABLE
            error_message += ERROR_CONTRADICTORY_CONSTRAINTS
            for constraint in contradictory_constraints:
                error_message += ERROR_CONSTRAINT_ITEM.format(constraint)

        # Create additional info section for equations if relevant
        additional_info = None
        if direct_constraints:
            additional_info = "Equations with this variable:\n"
            for constraint in direct_constraints:
                additional_info += f"  {constraint}\n"

        # Use the common feedback report function
        return self.create_feedback_report(
            goal_type="general",
            goal_token=variable_name,
            model_answer=model_answer,
            verifier_expected_answer=verifier_expected_answer,
            status=status,
            additional_info=additional_info,
            error_message=error_message,
            related_theorems=related_theorems,
            relevant_constraints=all_constraints,
            geometric_data=geometric_data
        )

    def find_relevant_constraints(self, variable_name, max_constraints=200):
        """
        Find all constraints relevant to a variable.
        This will find both direct constraints and constraints on related variables.

        Args:
            variable_name (str): The name of the variable to search for
            max_constraints (int): Maximum number of constraints to return

        Returns:
            dict: Dictionary with direct and related constraints
        """
        result = {
            "direct_constraints": [],  # Constraints that directly contain the variable
            "related_constraints": []  # Constraints on variables that appear with our target
        }

        # Regular expression to match the variable as a standalone identifier
        var_pattern = re.compile(r'(^|[^a-zA-Z0-9_])' + re.escape(variable_name) + r'([^a-zA-Z0-9_]|$)')

        # Track variables related to our target
        related_vars = set()

        # Keep track of all constraint strings we've seen to avoid duplicates
        seen_constraints = set()

        # First pass: find all direct constraints and collect related variables
        for c in self.solver.assertions():
            c_str = str(c)

            # Skip pi constant definitions
            if "pi ==" in c_str:
                continue

            # Check if this constraint directly involves our variable
            if var_pattern.search(c_str):
                formatted = self.format_constraint(c_str)

                # Only add if we haven't seen this formatted constraint before
                if formatted not in seen_constraints:
                    result["direct_constraints"].append(formatted)
                    seen_constraints.add(formatted)

                # Find variables in this constraint using different variable patterns
                for var_prefix in ["angle_", "length_", "arc_"]:
                    var_matches = re.findall(r'(' + var_prefix + r'\w+)', c_str)
                    for var_match in var_matches:
                        related_vars.add(var_match)

        # Second pass: find all constraints on related variables
        for c in self.solver.assertions():
            c_str = str(c)

            # Skip pi constants
            if "pi ==" in c_str:
                continue

            # Format constraint first to compare against seen_constraints
            formatted = self.format_constraint(c_str)

            # Skip if we've already seen this constraint
            if formatted in seen_constraints:
                continue

            # Check if any related variable appears in this constraint
            for var in related_vars:
                if var in c_str:
                    # Add to related constraints and mark as seen
                    result["related_constraints"].append(formatted)
                    seen_constraints.add(formatted)
                    break

        # Limit the number of constraints returned
        if max_constraints > 0:
            result["direct_constraints"] = result["direct_constraints"][:max_constraints // 2]
            result["related_constraints"] = result["related_constraints"][:max_constraints // 2]

        return result

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

    def generate_premise_error_feedback(self, theorem_name, args, premise, conclusions, error):
        """Generate user-friendly feedback for premise errors with complete theorem call information"""

        # Format the complete theorem call information
        args_str = ",".join(args)

        # Custom error message for premise errors
        error_message = TRIED_THEOREM.format(theorem_name, args_str, premise, str(conclusions))
        error_message += MISSING_PREMISE.format(error.message)

        # Include details if available and not empty
        if error.details and not (
                "Available parallel pairs: set()" in error.details or
                "Known parallel pairs: set()" in error.details or
                "Available" in error.details and "set()" in error.details or
                "Known" in error.details and "set()" in error.details
        ):
            error_message += DETAILS_PREFIX.format(error.details)

        # Get geometric facts
        geometric_data = self.gather_relevant_geometric_data()

        # Use the common feedback report function with customized error message
        return self.create_feedback_report(
            goal_type="premise_error",
            goal_token=theorem_name,
            model_answer=None,
            status="premise_violation",
            error_message=error_message,
            geometric_data=geometric_data,
            # No related theorems or constraints for premise errors
            related_theorems=[],
            relevant_constraints=[]
        )

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

    def check_value_constraint(self, goal_var, model_answer, epsilon=1e-8):
        """
        Check if a variable matches an expected value with appropriate constraints.

        Returns: (success, value, status)
        - success: True if variable can only be the expected value
        - value: Current/alternative value (for reporting)
        - status: "unique", "incompatible", "multiple_values", or "unsatisfiable"
        """
        if self.solver.check() == sat:
            model = self.solver.model()

            # First check if constraints allow the expected value
            temp_solver1 = Solver()
            for c in self.solver.assertions():
                temp_solver1.add(c)

            # Add constraint that goal_var == expected (within epsilon)
            temp_solver1.add(And(goal_var >= model_answer - epsilon, goal_var <= model_answer + epsilon))

            if temp_solver1.check() != sat:
                # Get current value
                try:
                    verifier_expected_answer = float(model.eval(goal_var).as_decimal(10).rstrip('?'))
                    return False, verifier_expected_answer, "incompatible"
                except Exception as e:
                    return False, None, f"Error computing value: {str(e)}"

            # Now check if any other value is allowed
            temp_solver2 = Solver()
            for c in self.solver.assertions():
                temp_solver2.add(c)

            # Add constraint: goal_var != expected (outside epsilon range)
            temp_solver2.add(Or(goal_var < model_answer - epsilon, goal_var > model_answer + epsilon))

            if temp_solver2.check() == sat:
                try:
                    alt_model = temp_solver2.model()
                    verifier_expected_answer = float(alt_model.eval(goal_var).as_decimal(10).rstrip('?'))
                    return False, verifier_expected_answer, "multiple_values"
                except Exception as e:
                    return False, None, f"Error computing alternative value: {str(e)}"

            # If we get here, the constraints uniquely determine the value
            return True, model_answer, "unique"
        else:
            return False, None, "unsatisfiable"

    def evaluate_expression(self, expr, mapping):
        """Evaluate a general expression using the provided mapping."""
        # Add math functions and constants
        import math
        mapping["pi"] = math.pi
        mapping["sqrt"] = math.sqrt

        # Add helper functions
        def Sub(x, y):
            return x - y

        mapping["Sub"] = Sub

        # Evaluate the expression
        return eval(expr, mapping)

    def validate_theorem_premises(self, theorem_name: str, args: List[str], premise: str) -> Tuple[ bool, Optional[GeometricError]]:
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
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
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
                                tier=ErrorTier.TIER2_PREMISE_VIOLATION,
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
                                tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                                message=f"Angles {angle1} and {angle2} must share a vertex",
                                details="Required for adjacent complementary angles"
                            ))

                        # Check that the shared point is in the collinear set
                        if shared_point not in points:
                            return return_error(GeometricError(
                                tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                                message=f"Shared point {shared_point} must be on the collinear line {points}",
                                details="Vertex must be on the collinear line"
                            ))

                        return True, None
                    else:
                        return return_error(GeometricError(
                            tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                            message="Invalid collinear points format in premise"
                        ))
                else:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing collinear points in premise",
                        details="adjacent_complementary_angle theorem requires collinear points"
                    ))
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem adjacent_complementary_angle"
                ))
        elif theorem_name == "bisector_of_angle_property_line_ratio":
            version = args[0]
            if version == "1":
                if len(args) < 3:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Insufficient arguments for bisector_of_angle_property_line_ratio",
                        details="Expected: bisector_of_angle_property_line_ratio(1, bisector, angle)"
                    ))

                bisector = args[1].strip()  # e.g., "BD"
                angle = args[2].strip()  # e.g., "ABC"

                # Check for angle bisector fact in premise
                bisector_match = re.search(
                    r'IsBisectorOfAngle\(' + re.escape(bisector) + r',' + re.escape(angle) + r'\)', premise)
                if not bisector_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Missing IsBisectorOfAngle({bisector},{angle}) in premise",
                        details="bisector_of_angle_property_line_ratio requires angle bisector fact"
                    ))

                # Check if angle bisector is stored in the system
                if hasattr(self, "angle_bisectors") and (bisector, angle) not in self.angle_bisectors:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Angle bisector {bisector} for angle {angle} not established",
                        details=f"Known angle bisectors: {self.angle_bisectors}"
                    ))

                # Check for collinearity fact in premise
                collinear_match = re.search(r'Collinear\((\w+)\)', premise)
                if not collinear_match:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message="Missing Collinear(...) fact in premise",
                        details="bisector_of_angle_property_line_ratio requires collinearity relationship"
                    ))

                collinear_points = collinear_match.group(1)

                # Check if this collinearity is stored in the system
                collinear_normalized = self.normalize_collinear_points(collinear_points)
                collinear_found = False
                for fact in self.collinear_facts:
                    fact_normalized = self.normalize_collinear_points(''.join(fact))
                    if fact_normalized == collinear_normalized:
                        collinear_found = True
                        break

                if not collinear_found:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Collinearity {collinear_points} not established",
                        details=f"Known collinear facts: {[''.join(fact) for fact in self.collinear_facts]}"
                    ))

                # Verify that the geometric setup is correct for the theorem
                # The bisector must connect a vertex of the angle to a point on the opposite side
                # The collinear points must include the endpoint of the bisector and the other two points

                # The angle vertex is the middle letter of the angle
                vertex = angle[1]

                # The bisector should start at the vertex
                if bisector[0] != vertex:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Bisector {bisector} doesn't start at angle vertex {vertex}",
                        details="The angle bisector must start at the angle's vertex"
                    ))

                # The collinear points should include the endpoint of the bisector
                # and the other two points of the triangle
                if bisector[1] not in collinear_points:
                    return return_error(GeometricError(
                        tier=ErrorTier.TIER2_PREMISE_VIOLATION,
                        message=f"Collinear points {collinear_points} don't include bisector endpoint {bisector[1]}",
                        details="The collinear points must include the endpoint of the bisector"
                    ))

                return True, None
            else:
                return return_error(GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message="these is no such version for the theorem",
                    details="these is no such version for the theorem bisector_of_angle_property_line_ratio"
                ))


    def parse_and_verify_proof(self, content: str) -> bool:
        def check_gt_answer(model_answer_numeric, model_answer_symbolic):
            """Check if GT_ANSWER exists and matches the model answer"""
            if not model_response_content:
                return True, ""

            end_idx = content.find("***MODEL_RESPONSE_END***")
            if end_idx == -1:
                return True, ""

            post_model_content = content[end_idx + len("***MODEL_RESPONSE_END***"):]
            gt_match = re.search(r'GT_ANSWER:\s*([^\s\n]+)', post_model_content)
            if not gt_match:
                return True, ""

            try:
                gt_answer_str = gt_match.group(1).strip()
                gt_answer_numeric, gt_answer_symbolic = parse_special_answer(gt_answer_str)

                if abs(gt_answer_numeric - model_answer_numeric) > epsilon:
                    # Create a more specific feedback message with clear "MODEL vs GROUND TRUTH" format
                    detailed_feedback = "verification failed.\n\n"
                    detailed_feedback += f"- Goal: value determination\n"
                    detailed_feedback += f"- Model answer: {model_answer_symbolic}\n"
                    detailed_feedback += f"- Verifier expected answer: {gt_answer_str}\n"
                    detailed_feedback += f"- Error: THE MODEL DETERMINED THE ANSWER TO BE {model_answer_symbolic} BUT IN THE GROUND TRUTH SOLUTION TO THE PROBLEM THE ANSWER IS {gt_answer_str}.\n"
                    detailed_feedback += f"  Please review your theorem sequence and ensure it correctly establishes the expected answer.\n\n"
                    detailed_feedback += "Please fix the proof."

                    print(
                        f"Model answer {model_answer_symbolic} ({model_answer_numeric}) differs from GT answer {gt_answer_str} ({gt_answer_numeric})")
                    return False, detailed_feedback
                return True, ""
            except Exception as e:
                print(f"Error comparing with GT_ANSWER: {e}")
                return True, ""  # Continue with regular verification on error
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

            # Extract content between MODEL_RESPONSE_BEGIN and MODEL_RESPONSE_END if present
            model_response_content = None
            gt_answer = None
            if len(content) > 0:
                start_marker = "***MODEL_RESPONSE_BEGIN***"
                end_marker = "***MODEL_RESPONSE_END***"
                start_idx = content.find(start_marker)

                if start_idx != -1:
                    start_idx += len(start_marker)
                    end_idx = content.find(end_marker, start_idx)

                    if end_idx != -1:
                        model_response_content = content[start_idx:end_idx].strip()

                        # Parse sections within the model response content
                        model_sections = {}
                        current_model_section = None

                        for line in model_response_content.split('\n'):
                            line = line.strip()
                            if not line:
                                continue

                            # Match any string ending with "ANSWER:" including "RETRY_ANSWER:"
                            if line.endswith("ANSWER:") or "_ANSWER:" in line:
                                current_model_section = ANSWER
                                model_sections[current_model_section] = []
                            # Match any string ending with "THEOREM_SEQUENCE:" including "RETRY_THEOREM_SEQUENCE:"
                            elif line.endswith("THEOREM_SEQUENCE:")or "_THEOREM_SEQUENCE:" in line:
                                current_model_section = THEOREM_SEQUENCE
                                model_sections[current_model_section] = []
                            elif current_model_section and line.endswith(':'):
                                current_model_section = line[:-1]
                                model_sections[current_model_section] = []
                            elif current_model_section:
                                model_sections[current_model_section].append(line)

                        # Override the original sections with the model response sections
                        if ANSWER in model_sections:
                            sections[ANSWER] = model_sections[ANSWER]
                        if THEOREM_SEQUENCE in model_sections:
                            sections[THEOREM_SEQUENCE] = model_sections[THEOREM_SEQUENCE]
                    else:
                        # --- ADDED ELSE BLOCK for missing END marker ---
                        # Start marker found, but end marker was NOT found after it
                        error_message = f"Found '{start_marker}' but could not find the '{end_marker}' marker afterwards."
                        print(f"Error: {error_message}")
                        # Create a TIER1 error object (optional, but good practice)
                        error = GeometricError(
                            tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                            message=error_message,
                            details="The proof structure is incorrect. Ensure both markers exist and are in the correct order."
                        )
                        # Return False with the formatted TIER1 error message
                        # Prioritize details if available, otherwise use message
                        error_content = error.details if error.details else error.message
                        return False, f"Error in {error.tier.name}: {error_content}"
                        # --- END OF ADDED ELSE BLOCK ---
                else:
                    # --- ADDED ELSE BLOCK for missing START marker ---
                    # Start marker was NOT found
                    error_message = f"Could not find the '{start_marker}' marker."
                    print(f"Error: {error_message}")
                    # Create a TIER1 error object
                    error = GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message=error_message,
                        details="The proof structure is incorrect. The required starting marker is missing."
                    )
                    # Return False with the formatted TIER1 error message
                    # Prioritize details if available, otherwise use message
                    error_content = error.details if error.details else error.message
                    return False, f"Error in {error.tier.name}: {error_content}"


            # adding all the points from the CONSTRUCTION_CDL_EXTENDED for the collinear
            if CONSTRUCTION_CDL_EXTENDED in sections:
                for line in sections[CONSTRUCTION_CDL_EXTENDED]:
                    if line.startswith('Point('):
                        name = line[6:-1]
                        self.add_point(name)

            if CONSTRUCTION_CDL in sections:
                print("\nProcessing CONSTRUCTION_CDL section...")
                for line in sections[CONSTRUCTION_CDL]:
                    print(f"Processing line: {line}")
                    if line.startswith('Collinear('):
                        points = line[10:-1]  # Extract points
                        normalized_points = self.normalize_collinear_points(points)
                        if normalized_points not in [''.join(fact) for fact in self.collinear_facts]:
                            self.collinear_facts.append(list(normalized_points))
                            self.add_collinear_fact(list(normalized_points))
                            print(f"Added normalized collinear points: {normalized_points}")
            # Process CONSTRUCTION_CDL_EXTENDED first

            if CONSTRUCTION_CDL_EXTENDED in sections:
                last_prefix = None
                current_type = None
                print("\nProcessing CONSTRUCTION_CDL_EXTENDED section...")
                for line in sections[CONSTRUCTION_CDL_EXTENDED]:
                    print(f"Processing line: {line}")
                    if line.startswith('Collinear('):
                        points = line[10:-1]  # Extract points from "Collinear(...)"

                        # If there are more than 3 points, break it down into all possible 3-point combinations
                        if len(points) > 3:
                            from itertools import combinations
                            for sub_points in combinations(points, 3):
                                three_points = ''.join(sub_points)
                                normalized_points = self.normalize_collinear_points(three_points)
                                normalized_str = ''.join(normalized_points)



                                # Otherwise, add it
                                self.collinear_facts.append(list(normalized_points))
                                self.add_collinear_fact(list(normalized_points))
                                print(f"Added normalized collinear points (extended): {normalized_points}")
                        else:
                            # Original behavior for 3 or fewer points
                            normalized_points = self.normalize_collinear_points(points)
                            normalized_str = ''.join(normalized_points)

                            # If the same fact appears in the main CONSTRUCTION_CDL section, skip it


                            # Otherwise, add it
                            self.collinear_facts.append(list(normalized_points))
                            self.add_collinear_fact(list(normalized_points))
                            print(f"Added normalized collinear points (extended): {normalized_points}")
                            # Handle lines starting with ".."
                            last_prefix = 'Collinear('
                    if line.startswith('..'):
                        print(f"Found dotted line, current_type is: {current_type}")  # Debug
                        if current_type is not None:
                            # Extract content inside the parentheses after ".."
                            match = re.search(r'\(\s*(.+?)\s*\)', line)
                            if match:
                                content = match.group(1)
                                print(f"Extracted content from dotted line: {content}")  # Debug

                                # Process based on current_type
                                if current_type == "Cocircular":
                                    # Process content as Cocircular data
                                    raw_fields = content.split(',')
                                    points = []
                                    for token in raw_fields:
                                        token = token.strip()
                                        # If token length > 1, expand into individual letters
                                        if len(token) > 1:
                                            points.extend(list(token))
                                        else:
                                            points.append(token)

                                    # Create canonical representation
                                    if points:
                                        fixed = points[0]
                                        others = sorted(points[1:])
                                        canonical = (fixed,) + tuple(others)
                                    else:
                                        canonical = tuple(points)

                                    self.cocircular_facts.append(canonical)
                                    print(f"Added cocircular fact from '..' line (canonical): {canonical}")
                                # Add other type handlers here
                            else:
                                print(f"Warning: Could not extract content from '..' line: {line}")
                        else:
                            print(f"Warning: Found '..' line without context: {line}")
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
                            last_prefix = 'ParallelBetweenLine('
                    if line.startswith('Line('):
                        match = re.match(r'Line\((\w+)\)', line)
                        if match:
                            line_name = match.group(1)
                            if len(line_name) == 2:  # Ensure it's a two-point line
                                normalized_line = self.normalize_line_name(line_name)
                                self.defined_lines.add(normalized_line)
                                print(f"Added defined line: {normalized_line}")
                                last_prefix = 'Line('
                            else:
                                print(f"Warning: Skipping invalid Line format: {line}")
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
                            last_prefix = 'Parallelogram('
                            current_type = "Parallelogram"
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
                            last_prefix = 'PerpendicularBetweenLine('
                    elif line.startswith("Arc("):
                        # Extract the arc name from e.g. "Arc(OBM)"
                        arc_name = line[4:-1].strip()
                        self.add_arc(arc_name)
                        last_prefix = 'Arc('
                    if line.startswith('Polygon('):
                        # Extract the polygon name; for instance, "ABC" from "Polygon(ABC)"
                        poly_match = re.match(r'Polygon\((\w+)\)', line)
                        if poly_match:
                            poly = poly_match.group(1)
                            # Normalize if you like (so that 'ABC' and 'BCA' are considered the same)
                            normalized_poly = self.normalize_triangle(poly) if len(poly) == 3 else poly
                            self.polygons.add(normalized_poly)
                            print(f"Added polygon: {normalized_poly}")
                            last_prefix = 'Polygon('
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
                        last_prefix = 'Circle('
                    elif line.startswith("Rhombus("):

                        match = re.match(r"Rhombus\((\w+)\)", line)

                        if match:
                            last_prefix = 'Rhombus('
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
                    elif line.startswith('Cocircular('):
                        # Process normal Cocircular line
                        inside = line[11:-1]  # This will be "B,UVTS" from "Cocircular(B,UVTS)"
                        raw_fields = inside.split(',')
                        points = []
                        for token in raw_fields:
                            token = token.strip()
                            # If token length > 1, expand into individual letters
                            if len(token) > 1:
                                points.extend(list(token))
                            else:
                                points.append(token)

                        # Create canonical representation
                        if points:
                            fixed = points[0]
                            others = sorted(points[1:])
                            canonical = (fixed,) + tuple(others)
                        else:
                            canonical = tuple(points)

                        self.cocircular_facts.append(canonical)
                        print(f"Added cocircular fact (canonical): {canonical}")
                        # Update current_type for potential ".." lines that follow
                        current_type = "Cocircular"
                        print(f"Set current_type to: {current_type}")  # Debug
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


            # Parse TEXT_CDL facts
            # Inside parse_and_verify_proof method
            # Inside parse_and_verify_proof method
            # Inside parse_and_verify_proof, when processing TEXT_CDL section:
            # Inside parse_and_verify_proof, modify the TEXT_CDL section:
            self.text_cdl_lines = []
            if TEXT_CDL in sections:
                self.text_cdl_lines = sections[TEXT_CDL]
                from fractions import Fraction
                for line in sections[TEXT_CDL]:
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
                            # Add this block to parse equilateral triangles
                    elif line.startswith('EquilateralTriangle('):
                        equilateral_match = re.match(r'EquilateralTriangle\((\w+)\)', line)
                        if equilateral_match:
                            triangle = equilateral_match.group(1)
                            print(f"Found equilateral triangle in TEXT_CDL: {triangle}")

                            # Initialize equilateral_triangles if needed
                            if not hasattr(self, "equilateral_triangles"):
                                self.equilateral_triangles = set()

                            # Add all cyclic rotations to the set
                            for i in range(len(triangle)):
                                rotation = triangle[i:] + triangle[:i]
                                self.equilateral_triangles.add(rotation)

                            # Since equilateral triangles are also isosceles triangles,
                            # add them to isosceles triangles set if it exists
                            if hasattr(self, "isosceles_triangles"):
                                for i in range(len(triangle)):
                                    rotation = triangle[i:] + triangle[:i]
                                    self.isosceles_triangles.add(rotation)
                            else:
                                # Create the isosceles_triangles set if it doesn't exist
                                self.isosceles_triangles = set()
                                for i in range(len(triangle)):
                                    rotation = triangle[i:] + triangle[:i]
                                    self.isosceles_triangles.add(rotation)

                            # Add constraint that all sides are equal
                            side1 = self.add_length(triangle[0], triangle[1])
                            side2 = self.add_length(triangle[1], triangle[2])
                            side3 = self.add_length(triangle[2], triangle[0])

                            self.solver.add(side1 == side2)
                            self.solver.add(side2 == side3)

                            # Add constraint that all angles equal 60°
                            angle1 = self.add_angle(triangle[0], triangle[1], triangle[2])
                            angle2 = self.add_angle(triangle[1], triangle[2], triangle[0])
                            angle3 = self.add_angle(triangle[2], triangle[0], triangle[1])

                            self.solver.add(angle1 == 60)
                            self.solver.add(angle2 == 60)
                            self.solver.add(angle3 == 60)

                            print(
                                f"Added equilateral triangle: {triangle} with all sides equal and all angles = 60°")
                    elif line.startswith('IsoscelesTriangle('):
                        match = re.match(r'IsoscelesTriangle\((\w+)\)', line)
                        if match:
                            triangle = match.group(1)
                            print(f"Found isosceles triangle in TEXT_CDL: {triangle}")

                            # Initialize isosceles_triangles if needed
                            if not hasattr(self, 'isosceles_triangles'):
                                self.isosceles_triangles = set()

                            # Add all rotations to handle different triangle representations
                            for i in range(len(triangle)):
                                rotation = triangle[i:] + triangle[:i]
                                self.isosceles_triangles.add(rotation)

                            # For a triangle ABC, assuming the pattern is:
                            # - Equal angles at B and C (second and third vertices)
                            # - Equal sides AB and AC (connecting first vertex to others)

                            # Add angle equality constraint
                            # For LNK, this would be angles LNK and NKL
                            angle1 = self.add_angle(triangle[0], triangle[1], triangle[2])  # LNK
                            angle2 = self.add_angle(triangle[1], triangle[2], triangle[0])  # NKL
                            self.solver.add(angle1 == angle2)
                            print(
                                f"Added isosceles triangle angle constraint: ∠{triangle[0]}{triangle[1]}{triangle[2]} = ∠{triangle[1]}{triangle[2]}{triangle[0]}")

                            # Add side equality constraint
                            # For LNK, this would be sides LN and LK
                            side1 = self.add_length(triangle[0], triangle[1])  # LN
                            side2 = self.add_length(triangle[0], triangle[2])  # LK
                            self.solver.add(side1 == side2)
                            print(
                                f"Added isosceles triangle side constraint: {triangle[0]}{triangle[1]} = {triangle[0]}{triangle[2]}")

                            # Store the theorem conclusion that would be generated
                            conclusion = f"Equal(MeasureOfAngle({triangle[0]}{triangle[1]}{triangle[2]}),MeasureOfAngle({triangle[1]}{triangle[2]}{triangle[0]}))"
                            if not hasattr(self, 'isosceles_conclusions'):
                                self.isosceles_conclusions = {}
                            self.isosceles_conclusions[triangle] = [conclusion]
                            print(f"Stored isosceles triangle conclusion: {conclusion}")
                        else:
                            print(f"Warning: Could not parse IsoscelesTriangle line: {line}")
                    elif line.startswith('MirrorCongruentBetweenTriangle('):
                        match = re.match(r'MirrorCongruentBetweenTriangle\((\w+),(\w+)\)', line)
                        if match:
                            tri1, tri2 = match.groups()
                            print(f"Found mirror congruent triangles in TEXT_CDL: {tri1} and {tri2}")
                            # Use the canonicalization function you provided
                            canonical_pair = self.canonicalize_mirror_congruent_triangle_pair(tri1, tri2)
                            # Store if not already present
                            if canonical_pair not in self.mirror_congruent_triangles:
                                self.mirror_congruent_triangles.append(canonical_pair)
                                print(
                                    f"Added mirror congruent triangles: {tri1} and {tri2} (canonical: {canonical_pair})")
                        else:
                            print(f"Warning: Could not parse MirrorCongruentBetweenTriangle line: {line}")
                    elif line.startswith('Equal(RadiusOfCircle('):
                        match = re.match(r'Equal\(RadiusOfCircle\((\w+)\),(.*?)\)', line)
                        if match:
                            circle_name, expression = match.groups()
                            expression = expression.strip()
                            print(f"Found radius value in TEXT_CDL: RadiusOfCircle({circle_name}) = {expression}")
                            try:
                                # Try parsing as numeric first
                                # Use Fraction for potentially better precision if input is like "1/5"
                                from fractions import Fraction
                                try:
                                    # Try Fraction first
                                    value = float(Fraction(expression))
                                except ValueError:
                                    # Fallback to direct float conversion
                                    value = float(expression)

                                # Get or create the radius variable
                                if circle_name not in self.circle_radii:
                                    self.circle_radii[circle_name] = Real(f"radius_{circle_name}")
                                    # Ensure radius is positive (or non-negative)
                                    self.solver.add(
                                        self.circle_radii[circle_name] > 0)  # Use > 0 for physical plausibility
                                radius_var = self.circle_radii[circle_name]

                                # Add the constraint
                                self.solver.add(radius_var == value)
                                print(f"Added numeric radius constraint: radius_{circle_name} = {value}")
                            except ValueError:
                                # Handle algebraic expression if necessary (less common for radius)
                                print(f"Warning: Could not parse radius value as numeric: {expression}")
                                variables = self.extract_variables(expression)
                                for var in variables:
                                    if var not in self.variables:
                                        self.variables[var] = Real(var)
                                        print(f"Created new variable for algebraic radius: {var}")
                                expr = self.parse_algebraic_expression(expression)
                                if circle_name not in self.circle_radii:
                                    self.circle_radii[circle_name] = Real(f"radius_{circle_name}")
                                    self.solver.add(self.circle_radii[circle_name] > 0)
                                radius_var = self.circle_radii[circle_name]
                                self.solver.add(radius_var == expr)
                                print(f"Added algebraic radius constraint: radius_{circle_name} = {expr}")
                    elif line.startswith('IsMidsegmentOfQuadrilateral('):
                        match = re.match(r'IsMidsegmentOfQuadrilateral\((\w+),(\w+)\)', line)
                        if match:
                            segment, quad = match.groups()

                            # Normalize quadrilateral name
                            norm_quad = self.normalize_quadrilateral(quad)

                            # Store both orientations of the segment
                            self.midsegments_of_quadrilaterals[(segment, norm_quad)] = True
                            self.midsegments_of_quadrilaterals[(segment[::-1], norm_quad)] = True

                            print(f"Recorded midsegment of quadrilateral: {segment} is a midsegment of {quad}")
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
                    elif line.startswith('MirrorSimilarBetweenTriangle('):
                        match = re.match(r'MirrorSimilarBetweenTriangle\((\w+),(\w+)\)', line)
                        if match:
                            tri1, tri2 = match.groups()
                            # You can reuse your existing canonicalization function
                            canonical_pair = self.canonicalize_mirror_triangle_pair(tri1, tri2)

                            if canonical_pair not in self.mirror_similar_triangles:
                                self.mirror_similar_triangles.append(canonical_pair)
                                print(
                                    f"Added mirror similar triangles: {tri1} and {tri2} (canonical: {canonical_pair})")
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

                            if len(triangle) != 3 or len(altitude_line) != 2:
                                print(f"Warning: Invalid format for altitude/triangle: {altitude_line}, {triangle}")
                                continue

                            vertex = None
                            for v_idx in range(len(triangle)):
                                if triangle[v_idx] == altitude_line[0]:  # Assume altitude starts at a vertex
                                    vertex = altitude_line[0]
                                    break
                                elif triangle[v_idx] == altitude_line[1]:  # Check other end too
                                    vertex = altitude_line[1]
                                    # Swap if vertex is second char in altitude_line
                                    altitude_line = altitude_line[::-1]
                                    break

                            if vertex is None:
                                print(
                                    f"Warning: Altitude line '{altitude_line}' doesn't start/end at a vertex of triangle '{triangle}'.")
                                continue

                            foot = altitude_line[1]  # The point where altitude meets the base (or its extension)
                            opposite_vertices = [v for v in triangle if v != vertex]

                            if len(opposite_vertices) != 2:
                                print(
                                    f"Warning: Could not identify opposite side for altitude {altitude_line} in {triangle}")
                                continue

                            # Add the 90-degree constraint.
                            # The angle is formed by one of the opposite vertices, the foot, and the vertex.
                            # Example: Altitude CD for triangle CAB. Vertex C, Foot D. Opposite A, B. Angle CDA = 90 or CDB = 90.
                            # Need collinearity (like ADB) to know which one. If D is *on* AB.
                            # Let's assume the standard case where the foot is on the opposite side segment.
                            # The angle is vertex-foot-opposite_vertex. e.g., CDB
                            angle_at_foot1 = self.add_angle(vertex, foot, opposite_vertices[0])
                            angle_at_foot2 = self.add_angle(vertex, foot, opposite_vertices[1])

                            # We need to determine which angle should be 90. Check collinearity.
                            base_collinear = None
                            foot_on_base_segment = False
                            for fact in self.collinear_facts:
                                fact_set = set(fact)
                                # Check if foot and opposite vertices are collinear
                                if foot in fact_set and set(opposite_vertices).issubset(fact_set):
                                    base_collinear = fact
                                    # Check if foot is BETWEEN the opposite vertices
                                    try:
                                        idx_f = fact.index(foot)
                                        idx_o1 = fact.index(opposite_vertices[0])
                                        idx_o2 = fact.index(opposite_vertices[1])
                                        if (idx_o1 < idx_f < idx_o2) or (idx_o2 < idx_f < idx_o1):
                                            foot_on_base_segment = True
                                    except ValueError:
                                        pass  # Point not found
                                    break

                            if foot_on_base_segment:
                                # If foot is between base vertices (e.g., ADB), both angles are 90
                                self.solver.add(angle_at_foot1 == 90)
                                self.solver.add(angle_at_foot2 == 90)
                                print(
                                    f"Added altitude constraints: ∠{vertex}{foot}{opposite_vertices[0]} = 90°, ∠{vertex}{foot}{opposite_vertices[1]} = 90°")
                            elif base_collinear:
                                # Foot is on the line extension. Assume one angle is 90. Which one?
                                # Convention needed. Let's assume the one involving the first opposite vertex?
                                self.solver.add(angle_at_foot1 == 90)
                                print(
                                    f"Added altitude constraint (foot on extension): ∠{vertex}{foot}{opposite_vertices[0]} = 90°")
                                # Could also infer the other is 180-90=90 if collinearity allows.
                                # self.solver.add(angle_at_foot2 == 90) # Might be redundant or incorrect depending on setup
                            else:
                                print(
                                    f"Warning: Collinearity of foot '{foot}' with base '{''.join(opposite_vertices)}' not established for altitude '{altitude_line}'. Cannot reliably set 90° angle.")

                            # Store the altitude fact if needed
                            if not hasattr(self, 'triangle_altitudes'): self.triangle_altitudes = []
                            self.triangle_altitudes.append((altitude_line, triangle))
                            if not hasattr(self, 'triangle_heights'):
                                self.triangle_heights = {}

                            # Get the length of the altitude line
                            altitude_length_var = self.add_length(altitude_line[0], altitude_line[1])

                            # Store this length as the height of the triangle
                            self.triangle_heights[triangle] = altitude_length_var
                            print(f"Connected altitude {altitude_line} as the height of triangle {triangle}")

                            # Also store for possible permutations of the triangle name
                            normalized_triangle = self.normalize_triangle(triangle)
                            for i in range(3):
                                variant = normalized_triangle[i:] + normalized_triangle[:i]
                                if variant != triangle:
                                    self.triangle_heights[variant] = altitude_length_var
                                    print(f"Also connected height to triangle variant {variant}")
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
                    elif line.startswith('Equal(Div(LengthOfLine('):
                        match = re.match(r'Equal\(Div\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\),(.+)\)', line)
                        if match:
                            line1, line2, expression = match.groups()
                            expression = expression.strip()
                            print(f"Found division length expression in TEXT_CDL: Div({line1},{line2}) = {expression}")

                            # Get Z3 variables for the lengths
                            try:
                                len1 = self.add_length(line1[0], line1[1])
                                len2 = self.add_length(line2[0], line2[1])
                            except IndexError:
                                print(f"Error: Invalid line name format in '{line}'. Skipping.")
                                continue  # Skip this line

                            # Try to parse the expression on the right side
                            div_val = None
                            numeric_ratio_value = None
                            try:
                                # Try Fraction first for precision (e.g., "3/2")
                                from fractions import Fraction
                                numeric_ratio_value = float(Fraction(expression))
                                div_val = numeric_ratio_value  # Use the numeric value for the constraint
                                print(f"Parsed division value as fraction: {numeric_ratio_value}")
                            except ValueError:
                                try:
                                    # Fallback: Try standard float conversion (e.g., "1.5")
                                    numeric_ratio_value = float(expression)
                                    div_val = numeric_ratio_value  # Use the numeric value
                                    print(f"Parsed division value as float: {numeric_ratio_value}")
                                except ValueError:
                                    try:
                                        # Fallback: Treat as algebraic expression (e.g., "x/2")
                                        print(f"Could not parse '{expression}' as numeric, treating as algebraic.")
                                        variables = self.extract_variables(expression)
                                        for var in variables:
                                            if var not in self.variables:
                                                self.variables[var] = Real(var)
                                        div_val = self.parse_algebraic_expression(expression)  # Z3 expression object
                                    except Exception as e_parse:
                                        print(
                                            f"Error parsing division expression '{expression}': {str(e_parse)}. Skipping constraint.")
                                        continue  # Skip adding this constraint

                            # --- Store Numeric Ratio if Found ---
                            if numeric_ratio_value is not None:
                                if not hasattr(self, 'numeric_length_ratios'):
                                    self.numeric_length_ratios = {}
                                norm_line1 = self.normalize_line_name(line1)
                                norm_line2 = self.normalize_line_name(line2)
                                # Store ratio L1/L2
                                self.numeric_length_ratios[(norm_line1, norm_line2)] = numeric_ratio_value
                                # Store ratio L2/L1 if value is non-zero
                                if abs(numeric_ratio_value) > 1e-9:
                                    self.numeric_length_ratios[(norm_line2, norm_line1)] = 1.0 / numeric_ratio_value
                                print(f"Stored known numeric ratio: {norm_line1}/{norm_line2} = {numeric_ratio_value}")
                            # --- End Storing ---

                            # Add the Z3 constraint
                            if div_val is not None:
                                # Use multiplication form: len1 == len2 * div_val
                                # This handles both numeric div_val and Z3 expression div_val
                                self.solver.add(len1 == len2 * div_val)
                                print(f"Added Z3 constraint: Length({line1}) == Length({line2}) * ({expression})")
                            else:
                                print(f"Warning: Could not determine value for constraint: {line}")
                    elif line.startswith('Equal(LengthOfLine(') and 'Mul(LengthOfLine(' in line:
                        # Handle cases like Equal(LengthOfLine(L1), Mul(LengthOfLine(L2), Value))
                        match = re.match(r'Equal\(LengthOfLine\((\w+)\),Mul\(LengthOfLine\((\w+)\),(.+)\)\)', line)
                        if match:
                            line1, line2, expression = match.groups()
                            expression = expression.strip()
                            print(
                                f"Found multiplication length expression: Length({line1}) = Length({line2}) * ({expression})")

                            # Get Z3 variables for the lengths
                            try:
                                len1 = self.add_length(line1[0], line1[1])
                                len2 = self.add_length(line2[0], line2[1])
                            except IndexError:
                                print(f"Error: Invalid line name format in '{line}'. Skipping.")
                                continue  # Skip this line

                            # Try to evaluate expression numerically
                            numeric_value = None
                            parsed_expr = None
                            try:
                                # Try simple float/fraction first
                                try:
                                    from fractions import Fraction
                                    numeric_value = float(Fraction(expression))
                                except ValueError:
                                    numeric_value = float(expression)
                                print(f"Parsed multiplier as numeric: {numeric_value}")
                                parsed_expr = numeric_value  # Use numeric value directly
                            except ValueError:
                                # Not a simple numeric value, treat as algebraic
                                print(f"Could not parse multiplier '{expression}' as numeric, treating as algebraic.")
                                try:
                                    variables = self.extract_variables(expression)
                                    for var in variables:
                                        if var not in self.variables:
                                            self.variables[var] = Real(var)
                                    parsed_expr = self.parse_algebraic_expression(expression)  # Z3 expression object
                                except Exception as e_parse:
                                    print(
                                        f"Error parsing multiplier expression '{expression}': {str(e_parse)}. Skipping constraint.")
                                    continue  # Skip adding this constraint

                            # --- Store Numeric Ratio if Found ---
                            if numeric_value is not None:
                                if not hasattr(self, 'numeric_length_ratios'):
                                    self.numeric_length_ratios = {}
                                norm_line1 = self.normalize_line_name(line1)
                                norm_line2 = self.normalize_line_name(line2)
                                # Store ratio L1/L2
                                self.numeric_length_ratios[(norm_line1, norm_line2)] = numeric_value
                                # Store ratio L2/L1 if value is non-zero
                                if abs(numeric_value) > 1e-9:
                                    self.numeric_length_ratios[(norm_line2, norm_line1)] = 1.0 / numeric_value
                                print(f"Stored known numeric ratio: {norm_line1}/{norm_line2} = {numeric_value}")
                            # --- End Storing ---

                            # Add the Z3 constraint
                            if parsed_expr is not None:
                                self.solver.add(len1 == len2 * parsed_expr)
                                print(f"Added Z3 constraint: Length({line1}) == Length({line2}) * ({expression})")
                            else:
                                print(f"Warning: Could not determine value for constraint: {line}")

                        # ... (elif block for 'Equal(LengthOfLine(' without Mul - standard numeric/algebraic assignment) ...
                        # This block should remain as you likely already have it, handling lines like:
                        # Equal(LengthOfLine(AB), 5) or Equal(LengthOfLine(CD), x)
                    elif line.startswith('Equal(LengthOfLine('):  # Assuming this is the fall-through case
                        match = re.match(r'Equal\(LengthOfLine\((\w+)\),(.+)\)', line)
                        if match:
                            line_name, expression = match.groups()
                            expression = expression.strip()
                            print(f"Found length assignment expression: Length({line_name}) = {expression}")
                            # Get (or create) the length variable
                            try:
                                length_var = self.add_length(line_name[0], line_name[1])
                            except IndexError:
                                print(f"Error: Invalid line name format '{line_name}' in '{line}'. Skipping.")
                                continue

                            # Parse and add constraint
                            parsed_val = None
                            try:
                                # Try numeric first
                                from fractions import Fraction
                                try:
                                    parsed_val = float(Fraction(expression))
                                except ValueError:
                                    parsed_val = float(expression)
                                print(f"Parsed assignment value as numeric: {parsed_val}")
                            except ValueError:
                                # Treat as algebraic
                                print(
                                    f"Could not parse assignment value '{expression}' as numeric, treating as algebraic.")
                                try:
                                    variables = self.extract_variables(expression)
                                    for var in variables:
                                        if var not in self.variables:
                                            self.variables[var] = Real(var)
                                    parsed_val = self.parse_algebraic_expression(expression)
                                except Exception as e_parse:
                                    print(
                                        f"Error parsing assignment expression '{expression}': {str(e_parse)}. Skipping constraint.")
                                    continue

                            if parsed_val is not None:
                                self.solver.add(length_var == parsed_val)
                                print(f"Added Z3 constraint: Length({line_name}) == {expression}")
                            else:
                                print(f"Warning: Could not determine value for constraint: {line}")
                    elif line.startswith("IsMedianOfTriangle("):
                        # Matches a fact like: IsMedianOfTriangle(AD,ABC)
                        match = re.match(r'IsMedianOfTriangle\((\w+),(\w{3})\)', line)
                        if match:
                            median_line, triangle = match.groups()

                            # Ensure the triangle name is valid
                            if len(triangle) != 3:
                                print(f"Error: Invalid triangle format in IsMedianOfTriangle({median_line},{triangle})")
                                continue

                            # Ensure median storage exists
                            if not hasattr(self, "medians"):
                                self.medians = []

                            # Store median information
                            self.medians.append((median_line, triangle))
                            print(f"Recorded median: IsMedianOfTriangle({median_line},{triangle})")

                            # Extract vertices
                            A, B, C = triangle

                            # Identify the midpoint of the opposite side
                            opposite_side = None
                            if median_line[0] in triangle:
                                opposite_side = [v for v in triangle if v != median_line[0]]
                            else:
                                print(f"Error: {median_line} does not start from a vertex of {triangle}")
                                continue

                            if len(opposite_side) != 2:
                                print(f"Error: Cannot determine opposite side for median {median_line}")
                                continue

                            M = median_line[1]  # Midpoint
                            X, Y = opposite_side  # The endpoints of the opposite side

                            # Store the midpoint property
                            if not hasattr(self, "midpoints"):
                                self.midpoints = {}

                            self.midpoints[(X, Y)] = M
                            self.midpoints[(Y, X)] = M

                            # Add equality constraint: XM = MY
                            len1 = self.add_length(X, M)
                            len2 = self.add_length(M, Y)
                            self.solver.add(len1 == len2)

                            # Ensure collinearity
                            collinear_points = [X, M, Y]
                            normalized_points = self.normalize_collinear_points(''.join(collinear_points))
                            if not any(set(collinear_points).issubset(set(''.join(fact))) for fact in
                                       self.collinear_facts):
                                self.collinear_facts.append(list(normalized_points))
                                self.add_collinear_fact(list(normalized_points))
                                print(f"Added collinearity constraint for median: {X}, {M}, {Y}")

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
                    elif line.startswith('RightTriangle('):
                        # Matches lines like: RightTriangle(BCA)
                        match = re.match(r'RightTriangle\((\w{3})\)', line)
                        if match:
                            triangle = match.group(1)
                            print(f"Found right triangle in TEXT_CDL: {triangle}")
                            normalized_triangle = self.normalize_triangle(triangle)

                            # Add to the set of known right triangles
                            if not hasattr(self, 'right_triangles'): self.right_triangles = set()
                            self.right_triangles.add(normalized_triangle)

                            # Assume the middle letter is the vertex with the right angle (convention)
                            # For BCA, the right angle is at C (angle BCA)
                            vertex = triangle[1]
                            p1 = triangle[0]
                            p3 = triangle[2]
                            right_angle_var = self.add_angle(p1, vertex, p3)

                            # Add the 90-degree constraint
                            self.solver.add(right_angle_var == 90)
                            print(f"Added right angle constraint based on RightTriangle fact: ∠{p1}{vertex}{p3} = 90°")
                        else:
                            print(f"Warning: Could not parse RightTriangle line: {line}")
                    elif line.startswith("Equal(AreaOfTriangle("):
                        # Matches lines like: Equal(AreaOfTriangle(ADC),9)
                        match = re.match(r'Equal\(AreaOfTriangle\((\w+)\),(.*)\)', line)
                        if match:
                            triangle, expression = match.groups()
                            expression = expression.strip()
                            normalized_triangle = ''.join(sorted(triangle))  # Normalize for lookup
                            print(f"Found triangle area in TEXT_CDL: AreaOfTriangle({triangle}) = {expression}")

                            # Create or get the area variable
                            if not hasattr(self, "triangle_areas"): self.triangle_areas = {}
                            if normalized_triangle not in self.triangle_areas:
                                self.triangle_areas[normalized_triangle] = Real(f"areaTriangle_{normalized_triangle}")
                                self.solver.add(self.triangle_areas[normalized_triangle] >= 0)
                            area_var = self.triangle_areas[normalized_triangle]

                            # Parse the expression (numeric or algebraic)
                            try:
                                eval_env = {"sqrt": math.sqrt, "pi": math.pi}
                                value = float(eval(expression, {"__builtins__": {}}, eval_env))
                                self.solver.add(area_var == value)
                                print(f"Added numeric triangle area constraint: Area({triangle}) = {value}")
                            except Exception:
                                print(f"Could not evaluate area as numeric: {expression}. Treating as algebraic.")
                                variables = self.extract_variables(expression)
                                for var in variables:
                                    if var not in self.variables: self.variables[var] = Real(var)
                                expr = self.parse_algebraic_expression(expression)
                                self.solver.add(area_var == expr)
                                print(f"Added algebraic triangle area constraint: Area({triangle}) = {expr}")
                        else:
                            print(f"Warning: Could not parse AreaOfTriangle line: {line}")



            print("\nCollected facts:")
            print("Collinear points:", self.collinear_facts)
            print("Parallel pairs:", self.parallel_pairs)
            print("Points:", list(self.points.keys()))

            # Process theorem sequence
            # Inside parse_and_verify_proof method
            # Process theorem sequence before verifying goal
            if THEOREM_SEQUENCE in sections:
                sequence_text = '\n'.join(sections[THEOREM_SEQUENCE])
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
                            # Validate premises first
                            # Validate premises first
                            is_valid, error = self.validate_theorem_premises(theorem_name, args, premise)
                            if not is_valid:
                                print(f"\nError in {error.tier.name}:")
                                # --- MODIFICATION START ---
                                if error.tier == ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION:
                                    # For TIER1, prioritize details for the feedback message
                                    error_content = error.details if error.details else error.message
                                    # Print details to console as well for clarity
                                    print(f"Details: {error_content}")
                                    # Construct the feedback string using the prioritized content
                                    feedback_message = f"Error in {error.tier.name}: {error_content}"
                                    # Return the specific feedback for TIER1
                                    return False, feedback_message
                                else:
                                    # For TIER2/TIER3, print message first, then details if available
                                    print(f"Message: {error.message}")
                                    if error.details:
                                        print(f"Details: {error.details}")
                                # --- MODIFICATION END ---

                                if error.tier == ErrorTier.TIER2_PREMISE_VIOLATION:
                                    # Use the special formatted feedback for premise errors
                                    return False, self.generate_premise_error_feedback(theorem_name, args, premise,
                                                                                       conclusions, error)
                                else:
                                    return False, f"Error in {error.tier.name}: {error.message}"

                            # Then process theorem step
                            # Then process theorem step
                            # Then process theorem step
                            error = self.adding_conclution(theorem_name, args, premise, conclusions)
                            if error:
                                print(f"\nError in {error.tier.name}:")
                                # --- MODIFICATION START ---
                                if error.tier == ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION:
                                    # For TIER1, prioritize details for the feedback message
                                    error_content = error.details if error.details else error.message
                                    # Print details to console as well for clarity
                                    print(f"Details: {error_content}")
                                    # Construct the feedback string using the prioritized content
                                    feedback_message = f"Error in {error.tier.name}: {error_content}"
                                    # Return the specific feedback for TIER1
                                    return False, feedback_message
                                else:
                                    # For TIER2/TIER3, print message first, then details if available
                                    print(f"Message: {error.message}")
                                    if error.details:
                                        print(f"Details: {error.details}")
                                # --- MODIFICATION END ---

                                if error.tier == ErrorTier.TIER2_PREMISE_VIOLATION:
                                    # Use the special formatted feedback for premise errors
                                    return False, self.generate_premise_error_feedback(theorem_name, args, premise,
                                                                                       conclusions, error)
                                else:
                                    return False, f"Error in {error.tier.name}: {error.message}"

            if GOAL_CDL in sections:
                goal_line = sections[GOAL_CDL][0]

                def parse_special_answer(answer_str):
                    """Parse answer strings including complex trigonometric expressions."""
                    import math
                    import re

                    # Store original symbolic form
                    original_symbolic = answer_str.strip()

                    # Remove whitespace
                    answer_str = answer_str.strip()

                    # Handle trig expressions with pi/180 conversion
                    if 'sin(' in answer_str.lower() or 'cos(' in answer_str.lower() or 'tan(' in answer_str.lower():
                        try:
                            # Replace pi with math.pi
                            modified_str = answer_str.replace('pi', 'math.pi')

                            # Create a safe environment with only math functions
                            safe_globals = {
                                'math': math,
                                'sin': math.sin,
                                'cos': math.cos,
                                'tan': math.tan,
                                'sqrt': math.sqrt
                            }

                            # Try direct evaluation with math functions
                            return float(eval(modified_str, {"__builtins__": {}}, safe_globals)), original_symbolic
                        except Exception as e:
                            print(f"Error evaluating trig expression: {e}")
                            # Continue to other methods if this fails

                    # Handle √ symbol format: 6(√6-1)
                    if '√' in answer_str:
                        # Handle pattern like "6(√6-1)"
                        pattern = r'(\d+)\(√(\d+)(-|\+)(\d+)\)'
                        match = re.match(pattern, answer_str)
                        if match:
                            a, b, op, c = match.groups()
                            a, b, c = float(a), float(b), float(c)
                            if op == '-':
                                return a * (math.sqrt(b) - c), original_symbolic
                            else:  # op == '+'
                                return a * (math.sqrt(b) + c), original_symbolic

                        # Handle pattern like "2√13"
                        pattern = r'(\d*)(√\d+)'
                        match = re.match(pattern, answer_str)
                        if match:
                            coef, sqrt_part = match.groups()
                            coef = 1 if coef == '' else float(coef)
                            sqrt_str = sqrt_part.replace('√', 'math.sqrt(') + ')'
                            try:
                                sqrt_val = eval(sqrt_str, {"math": math})
                                return coef * sqrt_val, original_symbolic
                            except Exception as e:
                                print(f"Error evaluating {sqrt_str}: {e}")
                                pass

                        # General replacement of √ symbol
                        try:
                            modified_str = re.sub(r'(\d*)√(\d+)', r'\1*math.sqrt(\2)', answer_str)
                            # Handle implicit multiplication
                            modified_str = re.sub(r'(\d+)\(', r'\1*(', modified_str)
                            return float(eval(modified_str, {"math": math})), original_symbolic
                        except Exception as e:
                            print(f"Error evaluating modified string '{modified_str}': {e}")
                            pass
                    if 'π' in answer_str:
                        # Pattern for (aπ)/b format
                        pattern = r'\((\d+)π\)/(\d+)'
                        match = re.match(pattern, answer_str)
                        if match:
                            a, b = match.groups()
                            a, b = float(a), float(b)
                            return (a * math.pi) / b, original_symbolic

                        # Pattern for aπ/b format (without parentheses)
                        pattern = r'(\d+)π/(\d+)'
                        match = re.match(pattern, answer_str)
                        if match:
                            a, b = match.groups()
                            a, b = float(a), float(b)
                            return (a * math.pi) / b, original_symbolic

                        # Handle other π expressions with general replacement
                        try:
                            # Replace π with math.pi for evaluation
                            modified_str = answer_str.replace('π', '*math.pi')
                            # Handle implicit multiplication and edge cases
                            modified_str = re.sub(r'(\d+)\(', r'\1*(', modified_str)
                            return float(eval(modified_str, {"math": math})), original_symbolic
                        except Exception as e:
                            print(f"Error evaluating π expression '{modified_str}': {e}")
                            pass
                    # Standard eval with math functions
                    try:
                        safe_globals = {
                            "pi": math.pi,
                            "sqrt": math.sqrt,
                            "sin": math.sin,
                            "cos": math.cos,
                            "tan": math.tan
                        }
                        return float(eval(answer_str, {"__builtins__": {}}, safe_globals)), original_symbolic
                    except Exception as e:
                        print(f"Error in standard eval: {e}")
                        # Fall back to Fraction
                        from fractions import Fraction
                        try:
                            return float(Fraction(answer_str)), original_symbolic
                        except Exception as e:
                            print(f"Error with Fraction conversion: {e}")
                            # Try numerical approximation for complex expressions
                            try:
                                # Replace mathematical functions with their math module equivalents
                                answer_str = answer_str.replace('sin', 'math.sin')
                                answer_str = answer_str.replace('cos', 'math.cos')
                                answer_str = answer_str.replace('tan', 'math.tan')
                                answer_str = answer_str.replace('pi', 'math.pi')

                                # Evaluate with a safe environment
                                result = eval(answer_str, {"__builtins__": {}}, {"math": math})
                                return float(result), original_symbolic
                            except Exception as e:
                                print(f"Error with numerical approximation: {e}")

                                # NEW CODE: Add SymPy as the last resort fallback method
                                try:
                                    # Import sympy only when needed
                                    from sympy import symbols, sympify, pi, N

                                    # Replace symbols with SymPy-compatible notation
                                    sympy_compatible = answer_str
                                    sympy_compatible = sympy_compatible.replace('π', 'pi')
                                    sympy_compatible = sympy_compatible.replace('√', 'sqrt')

                                    # Parse with SymPy's powerful expression parser
                                    expr = sympify(sympy_compatible)

                                    # Convert to floating point
                                    numeric_value = float(N(expr))

                                    print(f"Successfully parsed with SymPy: {numeric_value}")
                                    return numeric_value, original_symbolic
                                except Exception as e:
                                    print(f"Error parsing with SymPy: {e}")
                                    # If SymPy also fails, give up and raise the exception
                                    raise ValueError(f"Could not parse: {answer_str}")

                answer_str = sections[ANSWER][0].strip() if (ANSWER in sections and sections[ANSWER]) else None
                if answer_str is None:
                    return False, "No answer provided in ANSWER section."

                # Check for algebraic variables before trying to parse
                if self.contains_algebraic_variables(answer_str):
                    return False, "The final answer should be a numeric answer, you gave an expression with algebraic variable. Please fix your proof."

                try:
                    model_answer_numeric, model_answer_symbolic = parse_special_answer(answer_str)
                except Exception as e:
                    return False, f"Error parsing answer '{answer_str}': {str(e)}"
                    # Arc measure goal: Value(MeasureOfArc(X))
                epsilon = 1e-8  # Common epsilon value for all goals
                # Check against GT_ANSWER - if this fails, return early
                gt_check_result, gt_check_feedback = check_gt_answer(model_answer_numeric, model_answer_symbolic)
                if not gt_check_result:
                    return gt_check_result, gt_check_feedback
                arc_measure_match = re.search(r'Value\(MeasureOfArc\((\w+)\)\)', goal_line)
                if arc_measure_match:
                    arc_token = arc_measure_match.group(1)
                    print(f"\nGoal arc measure: {arc_token}")

                    normalized_arc = self.normalize_arc(arc_token)
                    arc_var_name = f"arc_{normalized_arc}"

                    if arc_var_name not in self.arcs:
                        error_msg = f"Arc {arc_token} is not defined in the system"
                        print(f"Error: {error_msg}")
                        return False, error_msg

                    arc_var = self.arcs[arc_var_name]
                    success, value, status = self.check_value_constraint(arc_var, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="arc_measure",
                            goal_token=arc_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for arc measure goal.")
                        return False, detailed_feedback

                # 2. Arc length goal: Value(LengthOfArc(X))
                arc_length_match = re.search(r'Value\(LengthOfArc\((\w+)\)\)', goal_line)
                if arc_length_match:
                    arc_token = arc_length_match.group(1)
                    print(f"\nGoal arc length: {arc_token}")


                    normalized_arc = self.normalize_arc(arc_token)
                    length_var_name = f"lengthArc_{normalized_arc}"
                    arc_length_var = Real(length_var_name)

                    success, value, status = self.check_value_constraint(arc_length_var, model_answer_numeric)

                    if success:
                        print(f"Success: Arc length {arc_token} is uniquely determined to be {model_answer_numeric}.")
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="arc_length",
                            goal_token=arc_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for arc length goal.")
                        return False, detailed_feedback

                radius_match = re.search(r'Value\(RadiusOfCircle\((\w+)\)\)', goal_line)
                if radius_match:
                    circle_token = radius_match.group(1)
                    print(f"\nGoal radius of circle: {circle_token}")

                    # Check if the circle has been defined
                    if not hasattr(self, 'circle_radii'):
                        self.circle_radii = {}

                    # Get or create the radius variable
                    if circle_token not in self.circle_radii:
                        radius_var = Real(f"radius_{circle_token}")
                        self.circle_radii[circle_token] = radius_var
                        self.solver.add(radius_var > 0)  # Radius must be positive
                    else:
                        radius_var = self.circle_radii[circle_token]

                    # Check if the value matches the expected answer
                    success, value, status = self.check_value_constraint(radius_var, model_answer_numeric)

                    if success:
                        print(
                            f"Success: Radius of circle {circle_token} is uniquely determined to be {model_answer_numeric}.")
                        return True, ""
                    else:
                        # Generate detailed feedback
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="radius",
                            goal_token=circle_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for circle radius goal.")
                        return False, detailed_feedback

                # Add this new goal handler in the parse_and_verify_proof method
                # (place it before the general_match block, after the radius_match handler we just added)

                # Reciprocal sum goal: Value(Add(Div(1,LengthOfLine(X)),Div(1,LengthOfLine(Y))))
                reciprocal_sum_match = re.search(
                    r'Value\(Add\(Div\(1,LengthOfLine\((\w+)\)\),Div\(1,LengthOfLine\((\w+)\)\)\)\)', goal_line)
                if reciprocal_sum_match:
                    line1 = reciprocal_sum_match.group(1)  # First line (e.g., "AM")
                    line2 = reciprocal_sum_match.group(2)  # Second line (e.g., "AN")

                    print(f"\nGoal reciprocal sum: 1/LengthOfLine({line1}) + 1/LengthOfLine({line2})")
                    goal_token = f"1/{line1}+1/{line2}"  # For feedback reporting

                    # Get the length variables for both lines
                    len1 = self.add_length(line1[0], line1[1])
                    len2 = self.add_length(line2[0], line2[1])

                    if self.solver.check() == sat:
                        model = self.solver.model()
                        try:
                            # Evaluate the lengths
                            len1_val = float(model.eval(len1).as_decimal(10).rstrip('?'))
                            len2_val = float(model.eval(len2).as_decimal(10).rstrip('?'))

                            # Check for division by zero
                            if abs(len1_val) < epsilon or abs(len2_val) < epsilon:
                                error_msg = "Division by zero in reciprocal sum"
                                print(f"Error: {error_msg}")
                                detailed_feedback = self.generate_detailed_feedback(
                                    goal_type="general",
                                    goal_token=goal_token,
                                    model_answer=model_answer_symbolic,
                                    status="insufficient_info",
                                    additional_info=f"Error: {error_msg}. Your proof constrains {line1} = {len1_val} or {line2} = {len2_val}, which would cause division by zero."
                                )
                                return False, detailed_feedback

                            # Calculate the expected answer: 1/len1 + 1/len2
                            verifier_expected_answer = (1.0 / len1_val) + (1.0 / len2_val)

                            # Check if the lengths are uniquely determined
                            temp_solver = Solver()
                            for c in self.solver.assertions():
                                temp_solver.add(c)

                            # Try to find alternative values for the lengths
                            temp_solver.add(Or(
                                len1 < len1_val - epsilon,
                                len1 > len1_val + epsilon,
                                len2 < len2_val - epsilon,
                                len2 > len2_val + epsilon
                            ))

                            if temp_solver.check() == sat:
                                # Multiple values possible
                                alt_model = temp_solver.model()
                                alt_len1_val = float(alt_model.eval(len1).as_decimal(10).rstrip('?'))
                                alt_len2_val = float(alt_model.eval(len2).as_decimal(10).rstrip('?'))

                                # Check for division by zero in the alternative solution
                                if abs(alt_len1_val) < epsilon or abs(alt_len2_val) < epsilon:
                                    print("Alternative solution involves division by zero, ignoring")
                                else:
                                    alt_sum = (1.0 / alt_len1_val) + (1.0 / alt_len2_val)

                                    # If the alternative sum is very close to the expected sum,
                                    # then the reciprocal sum might still be uniquely determined
                                    if abs(alt_sum - verifier_expected_answer) < epsilon:
                                        print(f"Alternative lengths give the same sum, continuing validation")
                                    else:
                                        # Generate detailed feedback for multiple values
                                        detailed_feedback = self.generate_detailed_feedback(
                                            goal_type="general",
                                            goal_token=goal_token,
                                            model_answer=model_answer_symbolic,
                                            verifier_expected_answer=None,
                                            status="multiple_values",
                                            additional_info=f"Your proof doesn't uniquely determine the value.\n"
                                        )
                                        return False, detailed_feedback

                            # Check if the computed value matches the expected answer
                            if abs(verifier_expected_answer - model_answer_numeric) < epsilon:
                                return True, ""
                            else:
                                # Generate detailed feedback for incompatible values
                                detailed_feedback = self.generate_detailed_feedback(
                                    goal_type="general",
                                    goal_token=goal_token,
                                    model_answer=model_answer_symbolic,
                                    verifier_expected_answer=verifier_expected_answer,
                                    status="incompatible",
                                    additional_info=f"Your proof constrains the lengths to {line1} = {len1_val} and {line2} = {len2_val},\n" +
                                                    f"which gives 1/{line1} + 1/{line2} = {verifier_expected_answer}, not {model_answer_numeric}."
                                )
                                return False, detailed_feedback

                        except Exception as e:
                            error_msg = f"Error calculating reciprocal sum: {str(e)}"
                            print(f"Error: {error_msg}")
                            return False, error_msg
                    else:
                        # Generate detailed feedback for unsatisfiable system
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="general",
                            goal_token=goal_token,
                            model_answer=model_answer_symbolic,
                            status="unsatisfiable"
                        )
                        return False, detailed_feedback



                triangle_area_match = re.search(r'Value\(AreaOfTriangle\((\w+)\)\)', goal_line)
                if triangle_area_match:
                    triangle_name = triangle_area_match.group(1)  # e.g., "CDB"
                    print(f"\nGoal type: Triangle Area ({triangle_name})")
                    print(f"Expected area: {model_answer_numeric}")

                    # Normalize the triangle name for dictionary lookup
                    normalized_triangle = ''.join(sorted(triangle_name))

                    # Check if the area variable exists
                    if not hasattr(self, "triangle_areas") or normalized_triangle not in self.triangle_areas:
                        error_msg = f"Area variable for triangle {triangle_name} (normalized: {normalized_triangle}) not defined by any theorem."
                        print(f"Error: {error_msg}")
                        # Known areas for debugging:
                        known_areas = list(getattr(self, 'triangle_areas', {}).keys())
                        print(f"Known triangle areas: {known_areas}")
                        return False, self.generate_detailed_feedback("triangle_area", triangle_name,
                                                                      model_answer_symbolic,
                                                                      status="insufficient_info",
                                                                      additional_info=error_msg)

                    triangle_area_var = self.triangle_areas[normalized_triangle]
                    self.solver.add(triangle_area_var>0)
                    # Check if the value matches the expected answer
                    success, value, status = self.check_value_constraint(triangle_area_var, model_answer_numeric, epsilon=epsilon)

                    if success:
                        print(f"Success: The area of triangle {triangle_name} is uniquely determined to be {model_answer_numeric}.")
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="triangle_area",
                            goal_token=triangle_name,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for triangle area goal.")
                        return False, detailed_feedback
                    # --- END OF ADDED BLOCK ---




                # Add this after other goal type checks like arc_measure, length, etc.
                quad_perimeter_match = re.search(r'Value\(PerimeterOfQuadrilateral\((\w+)\)\)', goal_line)
                if quad_perimeter_match:
                    quad_name = quad_perimeter_match.group(1)
                    print(f"\nGoal quadrilateral perimeter: {quad_name}")
                    print(f"Expected perimeter: {model_answer_numeric}")

                    # Create or get the perimeter variable for this quadrilateral
                    if not hasattr(self, "quadrilateral_perimeters"):
                        self.quadrilateral_perimeters = {}

                    if quad_name not in self.quadrilateral_perimeters:
                        perimeter_var = Real(f"perimeter_{quad_name}")
                        self.quadrilateral_perimeters[quad_name] = perimeter_var
                    else:
                        perimeter_var = self.quadrilateral_perimeters[quad_name]

                    # Check if the perimeter matches the model answer
                    success, value, status = self.check_value_constraint(perimeter_var, model_answer_numeric)

                    if success:
                        print(
                            f"Success: Quadrilateral perimeter {quad_name} is uniquely determined to be {model_answer_numeric}.")
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="quadrilateral_perimeter",
                            goal_token=quad_name,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for quadrilateral perimeter goal.")
                        return False, detailed_feedback

                sum_angles_match = re.search(r'Value\(Add\(MeasureOfAngle\((\w+)\),MeasureOfAngle\((\w+)\)\)\)',
                                             goal_line)
                if sum_angles_match:
                    angle1_token = sum_angles_match.group(1)
                    angle2_token = sum_angles_match.group(2)
                    goal_token = f"{angle1_token}+{angle2_token}"  # For feedback reporting
                    print(f"\nGoal type: Sum of Angles ({goal_token})")

                    # Get the Z3 variables for the angles
                    angle1_var = self.add_angle(angle1_token[0], angle1_token[1], angle1_token[2])
                    angle2_var = self.add_angle(angle2_token[0], angle2_token[1], angle2_token[2])

                    # Create the sum expression
                    sum_expr = angle1_var + angle2_var

                    # Check if the value matches the expected answer
                    success, value, status = self.check_value_constraint(sum_expr, model_answer_numeric, epsilon=epsilon)

                    if success:

                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="sum_angle",  # Use a descriptive type
                            goal_token=goal_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status,
                            # Add info about individual angles if helpful
                            additional_info=f"Angle 1: {angle1_token}\nAngle 2: {angle2_token}"
                        )
                        print(f"Detailed feedback generated for sum of angles goal.")
                        return False, detailed_feedback

                sum_lengths_match = re.search(r'Value\(Add\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)', goal_line)
                if sum_lengths_match:
                    line1 = sum_lengths_match.group(1)
                    line2 = sum_lengths_match.group(2)

                    print(f"\nGoal sum of lengths: LengthOfLine({line1}) + LengthOfLine({line2})")


                    len1 = self.add_length(line1[0], line1[1])
                    len2 = self.add_length(line2[0], line2[1])
                    sum_expr = len1 + len2

                    success, value, status = self.check_value_constraint(sum_expr, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        goal_token = f"{line1}+{line2}"  # Create a combined token
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="sum",
                            goal_token=goal_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for sum of lengths goal.")
                        return False, detailed_feedback

                # Cosine goal: Value(Cos(MeasureOfAngle(XXX)))
                # Cosine goal: Value(Cos(MeasureOfAngle(XXX)))
                cosine_match = re.search(r'Value\(Cos\(MeasureOfAngle\((\w+)\)\)\)', goal_line)
                if cosine_match:
                    angle_token = cosine_match.group(1)
                    print(f"\nGoal cosine: Cos(MeasureOfAngle({angle_token}))")

                    success, value, status = self.evaluate_trig_function("cos", angle_token, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="cosine",
                            goal_token=angle_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for cosine goal.")
                        return False, detailed_feedback

                sin_match = re.search(r'Value\(Sin\(MeasureOfAngle\((\w+)\)\)\)', goal_line)
                if sin_match:
                    angle_token = sin_match.group(1)
                    print(f"\nGoal sine: Sin(MeasureOfAngle({angle_token}))")

                    success, value, status = self.evaluate_trig_function("sin", angle_token, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="sine",
                            goal_token=angle_token,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for sine goal.")
                        return False, detailed_feedback

                # Sine goal and other goal types would follow a similar pattern, using the common
                # check_value_constraint function where possible and handling special cases as needed
                # 6. Division of lengths goal: Value(Div(LengthOfLine(AF),LengthOfLine(AC)))
                length_div_match = re.search(r'Value\(Div\(LengthOfLine\((\w+)\),LengthOfLine\((\w+)\)\)\)', goal_line)
                if length_div_match:
                    line1 = length_div_match.group(1)  # Numerator line
                    line2 = length_div_match.group(2)  # Denominator line

                    print(f"\nGoal division of lengths: Div(LengthOfLine({line1}),LengthOfLine({line2}))")

                    len1 = self.add_length(line1[0], line1[1])
                    len2 = self.add_length(line2[0], line2[1])

                    if self.solver.check() == sat:
                        model = self.solver.model()
                        try:
                            val1 = float(model.eval(len1).as_decimal(10).rstrip('?'))
                            val2 = float(model.eval(len2).as_decimal(10).rstrip('?'))

                            # Check for division by zero
                            if abs(val2) < epsilon:
                                error_msg = "Division by zero in length ratio"
                                print("Error: Division by zero in length ratio")
                                return False, error_msg

                            verifier_expected_answer = val1 / val2

                            # Check if the division is uniquely determined
                            temp_solver = Solver()
                            for c in self.solver.assertions():
                                temp_solver.add(c)

                            # We want to check if len1/len2 can have a different value
                            temp_solver.add(
                                Or(
                                    len1 < (model_answer_numeric - epsilon) * len2,
                                    len1 > (model_answer_numeric + epsilon) * len2
                                )
                            )

                            if temp_solver.check() == sat:
                                alt_model = temp_solver.model()
                                alt_val1 = float(alt_model.eval(len1).as_decimal(10).rstrip('?'))
                                alt_val2 = float(alt_model.eval(len2).as_decimal(10).rstrip('?'))

                                if abs(alt_val2) < epsilon:
                                    # Skip this alternative since it involves division by zero
                                    print("Note: Found an alternative solution but it involves division by zero")
                                    alt_ratio = None
                                    status = "multiple_values"
                                else:
                                    alt_ratio = alt_val1 / alt_val2
                                    status = "multiple_values"

                                # Generate detailed feedback for multiple values
                                goal_token = f"{line1}/{line2}"
                                detailed_feedback = self.generate_detailed_feedback(
                                    goal_type="ratio",
                                    goal_token=goal_token,
                                    model_answer=model_answer_symbolic,
                                    verifier_expected_answer=alt_ratio,
                                    status=status,
                                    additional_info=""
                                )
                                print(f"Detailed feedback generated for division goal.")
                                return False, detailed_feedback

                            # Check if computed value matches expected value
                            if abs(verifier_expected_answer - model_answer_numeric) >= epsilon:
                                # Generate detailed feedback for incompatible value
                                goal_token = f"{line1}/{line2}"
                                detailed_feedback = self.generate_detailed_feedback(
                                    goal_type="ratio",
                                    goal_token=goal_token,
                                    model_answer=model_answer_symbolic,
                                    verifier_expected_answer=verifier_expected_answer,
                                    status="incompatible",
                                    additional_info=f"Your proof constrains the ratio to {verifier_expected_answer:.6f}"
                                )
                                print(f"Detailed feedback generated for division goal.")
                                return False, detailed_feedback


                            return True, ""
                        except Exception as e:
                            error_msg = f"Error converting length values: {str(e)}"
                            print("Error converting length values:", e)
                            return False, error_msg
                    else:
                        # Generate detailed feedback for unsatisfiable
                        goal_token = f"{line1}/{line2}"
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="ratio",
                            goal_token=goal_token,
                            model_answer=model_answer_symbolic,
                            status="unsatisfiable"
                        )
                        print(f"Detailed feedback generated for division goal.")
                        return False, detailed_feedback

                perimeter_match = re.search(r'Value\(PerimeterOfTriangle\((\w+)\)\)', goal_line)
                if perimeter_match:
                    triangle = perimeter_match.group(1)
                    print(f"\nDetected perimeter goal: PerimeterOfTriangle({triangle})")
                    print(f"\nGoal triangle perimeter: {triangle}")

                    if triangle in self.triangle_perimeters:
                        perimeter_var = self.triangle_perimeters[triangle]
                    else:
                        perimeter_var = self.calculate_perimeter(triangle)
                        self.triangle_perimeters[triangle] = perimeter_var

                    success, value, status = self.check_value_constraint(perimeter_var, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="perimeter",
                            goal_token=triangle,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status,
                            additional_info=f"Triangle sides:\n" +
                                            f"  {triangle[0]}{triangle[1]}: {self.add_length(triangle[0], triangle[1])}\n" +
                                            f"  {triangle[1]}{triangle[2]}: {self.add_length(triangle[1], triangle[2])}\n" +
                                            f"  {triangle[2]}{triangle[0]}: {self.add_length(triangle[2], triangle[0])}"
                        )
                        print(f"Detailed feedback generated for perimeter goal.")
                        return False, detailed_feedback

                    # 8. Length goal: Value(LengthOfLine(AB))
                length_match = re.search(r'Value\(LengthOfLine\((\w+)\)\)', goal_line)
                if length_match:
                    line_name = length_match.group(1)
                    print(f"\nGoal line: {line_name}")

                    # Get the length variable
                    length_var = self.add_length(line_name[0], line_name[1])

                    success, value, status = self.check_value_constraint(length_var, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="length",
                            goal_token=line_name,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for length goal.")
                        return False, detailed_feedback

                angle_match = re.search(r'Value\(MeasureOfAngle\((\w+)\)\)', goal_line)
                if angle_match:
                    goal_angle = angle_match.group(1)
                    print(f"\nGoal angle: {goal_angle}")

                    angle_var = self.add_angle(goal_angle[0], goal_angle[1], goal_angle[2])

                    success, value, status = self.check_value_constraint(angle_var, model_answer_numeric)

                    if success:
                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="angle",
                            goal_token=goal_angle,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for angle goal.")
                        return False, detailed_feedback

                    # 10. Quadrilateral area goal: Value(AreaOfQuadrilateral(ABCD))
                quad_area_match = re.search(r'Value\(AreaOfQuadrilateral\((\w+)\)\)', goal_line)
                if quad_area_match:
                    quad_name = quad_area_match.group(1)
                    print(f"\nDetected quadrilateral area goal: AreaOfQuadrilateral({quad_name})")
                    print(f"\nGoal quadrilateral area: {quad_name}")

                    if quad_name in self.quad_areas:
                        quad_area_var = self.quad_areas[quad_name]
                    else:
                        quad_area_var = Real(f"AreaOfQuadrilateral_{quad_name}")
                        self.quad_areas[quad_name] = quad_area_var

                    success, value, status = self.check_value_constraint(quad_area_var, model_answer_numeric)

                    if success:

                        return True, ""
                    else:
                        # Generate detailed feedback report
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="quad_area",
                            goal_token=quad_name,
                            model_answer=model_answer_symbolic,
                            verifier_expected_answer=value,
                            status=status
                        )
                        print(f"Detailed feedback generated for quadrilateral area goal.")
                        return False, detailed_feedback
                general_match = re.search(r'Value\((.+)\)', goal_line)
                if general_match:
                    goal_expr = general_match.group(1).strip()
                    print(f"\nGeneral goal expression: {goal_expr}")

                    # Special handling for Sub expressions
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

                                # Check the value constraint for the difference
                                diff_expr = angle1_var - angle2_var
                                success, value, status = self.check_value_constraint(diff_expr, model_answer_numeric)

                                if success:
                                    return True, ""
                                else:
                                    # Generate detailed feedback for angle subtraction
                                    detailed_feedback = self.generate_detailed_feedback(
                                        goal_type="general",
                                        goal_token=f"Sub({expr1_str},{expr2_str})",
                                        model_answer=model_answer_symbolic,
                                        verifier_expected_answer=value,
                                        status=status,
                                        additional_info=f"Angle 1: {angle1_name}\nAngle 2: {angle2_name}"
                                    )
                                    print(f"Detailed feedback generated for angle subtraction goal.")
                                    return False, detailed_feedback

                    # Special handling for single variables (most common case)
                    elif len(goal_expr) == 1 and goal_expr.isalpha() and goal_expr in self.variables:
                        # Get the Z3 variable directly
                        var = self.variables[goal_expr]

                        # Use the existing check_value_constraint function that handles multiple solutions
                        success, value, status = self.check_value_constraint(var, model_answer_numeric)

                        if success:
                            return True, ""
                        else:
                            # Generate detailed feedback with proper status
                            detailed_feedback = self.generate_detailed_feedback(
                                goal_type="general",
                                goal_token=goal_expr,
                                model_answer=model_answer_symbolic,
                                verifier_expected_answer=value,
                                status=status,
                                additional_info=f"Variable {goal_expr} is {'not uniquely determined' if status == 'multiple_values' else 'incompatible with expected value'}"
                            )
                            print(f"Detailed feedback generated for variable goal.")
                            return False, detailed_feedback

                    # For other general expressions, build a mapping for evaluation
                    if self.solver.check() == sat:
                        model = self.solver.model()

                        # Build mapping for variables and try to evaluate the expression
                        try:
                            # Build mapping for variables
                            mapping = {}
                            for var, z3var in self.variables.items():
                                try:
                                    val = model.eval(z3var, model_completion=True)
                                    val_str = str(val).replace('?', '')
                                    from fractions import Fraction
                                    mapping[var] = float(Fraction(val_str))
                                except Exception as e:
                                    print(f"Error converting free variable {var}: {e}")

                            # Add circle areas and triangle areas if needed
                            for circle, var in self.circle_areas.items():
                                value = model.eval(var)
                                value_str = str(value).replace('?', '')
                                try:
                                    from fractions import Fraction
                                    mapping[f"ac_{circle.lower()}"] = float(Fraction(value_str))
                                except Exception as e:
                                    print("Error converting circle area for", circle, ":", e)

                            for tri, var in self.triangle_areas.items():
                                value = model.eval(var)
                                value_str = str(value).replace('?', '')
                                try:
                                    from fractions import Fraction
                                    mapping[f"at_{tri.lower()}"] = float(Fraction(value_str))
                                except Exception as e:
                                    print("Error converting triangle area for", tri, ":", e)

                            # Evaluate the expression
                            verifier_expected_answer = self.evaluate_expression(goal_expr, mapping)

                            if abs(verifier_expected_answer - model_answer_numeric) < epsilon:
                                return True, ""
                            else:
                                # Generate detailed feedback for general expression
                                detailed_feedback = self.generate_detailed_feedback(
                                    goal_type="general",
                                    goal_token=goal_expr,
                                    model_answer=model_answer_symbolic,
                                    verifier_expected_answer=verifier_expected_answer,
                                    status="incompatible",
                                    additional_info=f"Evaluated expression: {goal_expr}\nComputed value: {verifier_expected_answer}\nExpected value: {model_answer_symbolic}"
                                )
                                print(f"Detailed feedback generated for general goal expression.")
                                return False, detailed_feedback
                        except Exception as e:
                            error_msg = f"Error evaluating general goal expression: {str(e)}"
                            print(f"Error evaluating general goal expression: {e}")
                            return False, error_msg
                    else:
                        # Generate detailed feedback for unsatisfiable
                        detailed_feedback = self.generate_detailed_feedback(
                            goal_type="general",
                            goal_token=goal_expr,
                            model_answer=model_answer_symbolic,
                            status="unsatisfiable"
                        )
                        print(f"Detailed feedback generated for general goal expression.")
                        return False, detailed_feedback

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

    def collect_related_facts(self, goal_points, goal_type=None):
        """
        Collect only facts that directly involve the goal token and are meaningful for debugging
        Filters out trivial elements like individual points and basic angles
        """
        related_facts = {}
        goal_points_set = set(goal_points)
        goal_token = ''.join(goal_points)

        # 1. Check for perpendicular lines relevant to the goal
        perp_facts = []
        seen_perp_pairs = set()

        for pair in self.perpendicular_pairs:
            line1, line2 = pair

            # Check if at least one point from goal is in these lines
            if any(p in line1 for p in goal_points) or any(p in line2 for p in goal_points):
                # Create a normalized key to avoid duplicates
                key = tuple(sorted([line1, line2]))
                if key not in seen_perp_pairs:
                    seen_perp_pairs.add(key)
                    perp_facts.append(f"{line1} ⊥ {line2}")

        if perp_facts:
            related_facts["Perpendicular Lines"] = perp_facts

        # 2. Check for specific angle values in TEXT_CDL
        if goal_type == "angle":
            angle_values = []

            if hasattr(self, 'text_cdl_lines'):
                for line in self.text_cdl_lines:
                    # Look for direct values for this angle
                    angle_match = re.search(r'Equal\(MeasureOfAngle\(' + re.escape(goal_token) + r'\),(.+?)\)', line)
                    if angle_match:
                        value = angle_match.group(1).strip()
                        angle_values.append(f"∠{goal_token} = {value}")

            if angle_values:
                related_facts["Angle Values"] = angle_values

        # 3. Check for parallel lines involving goal points
        parallel_facts = []
        seen_parallel = set()

        for pair in self.parallel_pairs:
            line1, line2 = pair

            # Check if at least one point from goal is in these lines
            if any(p in line1 for p in goal_points) or any(p in line2 for p in goal_points):
                # Create a normalized key to avoid duplicates
                key = tuple(sorted([line1, line2]))
                if key not in seen_parallel:
                    seen_parallel.add(key)
                    parallel_facts.append(f"{line1} ∥ {line2}")

        if parallel_facts:
            related_facts["Parallel Lines"] = parallel_facts

        # 4. Check for special quadrilaterals
        # First, find relevant quadrilaterals that contain points from our goal
        special_quads = []
        seen_quads = set()

        for quad in self.polygons:
            if len(quad) == 4 and any(p in quad for p in goal_points):
                # Skip if we've already seen a cyclic variation of this quad
                normalized = min(quad[i:] + quad[:i] for i in range(len(quad)))
                if normalized in seen_quads:
                    continue
                seen_quads.add(normalized)

                properties = []
                # Check for various quadrilateral types
                if quad in self.parallelograms or any(
                        var in self.parallelograms for var in get_cyclic_variations(quad)):
                    properties.append("parallelogram")

                if hasattr(self, 'rectangles'):
                    if quad in self.rectangles or any(
                            var in self.rectangles for var in get_cyclic_variations_rectangle(quad)):
                        properties.append("rectangle")

                if hasattr(self, 'squares'):
                    if quad in self.squares or any(
                            var in self.squares for var in get_cyclic_variations_rectangle(quad)):
                        properties.append("square")

                if hasattr(self, 'rhombi'):
                    if quad in self.rhombi or any(var in self.rhombi for var in get_cyclic_variations_rectangle(quad)):
                        properties.append("rhombus")

                if properties:
                    special_quads.append(f"Quadrilateral {quad} ({', '.join(properties)})")

        if special_quads:
            related_facts["Special Quadrilaterals"] = special_quads

        # 5. Check for collinear facts involving goal points
        collinear_facts = []
        for collinear in self.collinear_facts:
            if any(p in collinear for p in goal_points) and len(collinear) >= 3:
                collinear_facts.append(f"Collinear {''.join(collinear)}")

        if collinear_facts:
            related_facts["Collinear Points"] = collinear_facts

        # 6. Check for special triangles
        special_triangles = []
        seen_triangles = set()

        for triangle in self.polygons:
            if len(triangle) == 3 and any(p in triangle for p in goal_points):
                # Skip if we've already seen a cyclic variation
                normalized = self.normalize_triangle(triangle)
                if normalized in seen_triangles:
                    continue
                seen_triangles.add(normalized)

                properties = []
                # Check for right triangle
                if triangle in self.right_triangles or normalized in self.right_triangles:
                    properties.append("right")

                # Check for isosceles
                if hasattr(self, 'isosceles_triangles'):
                    if triangle in self.isosceles_triangles or normalized in self.isosceles_triangles:
                        properties.append("isosceles")

                if properties:
                    special_triangles.append(f"Triangle {triangle} ({', '.join(properties)})")

        if special_triangles:
            related_facts["Special Triangles"] = special_triangles

        # Remove empty categories
        return {k: v for k, v in related_facts.items() if v}

    def find_related_theorems_for_variable(self, variable_name):
        """Find theorems that directly or indirectly constrain a variable goal."""
        related_theorems = []

        # First, identify all angle or length expressions defined in terms of the goal variable
        related_expressions = []
        related_angles = []
        related_lengths = []

        if hasattr(self, 'text_cdl_lines'):
            for line in self.text_cdl_lines:
                if variable_name in line:
                    # Look for angles defined in terms of goal_variable
                    angle_match = re.search(r'Equal\(MeasureOfAngle\((\w+)\),(.*?)\)', line)
                    if angle_match and variable_name in angle_match.group(2):
                        angle_token = angle_match.group(1)
                        related_expressions.append(f"MeasureOfAngle({angle_token})")
                        related_angles.append(angle_token)

                    # Look for lengths defined in terms of goal_variable
                    length_match = re.search(r'Equal\(LengthOfLine\((\w+)\),(.*?)\)', line)
                    if length_match and variable_name in length_match.group(2):
                        length_token = length_match.group(1)
                        related_expressions.append(f"LengthOfLine({length_token})")
                        related_lengths.append(length_token)

        # Now search for theorems that constrain these expressions
        for theorem_info in self.theorem_sequence:
            is_related = False

            # Check if goal variable is directly mentioned
            if variable_name in theorem_info["premise"] or any(variable_name in arg for arg in theorem_info["args"]):
                is_related = True

            # Check if any conclusion constrains a related expression
            if not is_related:
                for conclusion in theorem_info["conclusions"]:
                    # Check for direct mentions of related expressions
                    for expr in related_expressions:
                        if expr in conclusion:
                            is_related = True
                            break

                    # Also check for any angle tokens in the conclusion
                    for angle in related_angles:
                        if angle in conclusion:
                            is_related = True
                            break

                    if is_related:
                        break

            if is_related:
                related_theorems.append({
                    "step": theorem_info["step_number"],
                    "theorem": theorem_info["theorem_name"],
                    "args": theorem_info["args"],
                    "conclusion": ", ".join(theorem_info["conclusions"])
                })

        return related_theorems

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

    def contains_algebraic_variables(self, expr: str) -> bool:
        """Check if an expression contains algebraic variables (letters that aren't part of math functions)."""
        import re

        # First remove all numbers from the expression
        expr_without_nums = re.sub(r'\d+(\.\d+)?', '', expr)

        # Remove operators and parentheses
        expr_clean = re.sub(r'[+\-*/()^]', '', expr_without_nums)

        # Remove known math constants and functions
        math_terms = ['pi', 'sqrt', 'sin', 'cos', 'tan', 'log', 'ln', 'exp']
        for term in math_terms:
            expr_clean = expr_clean.lower().replace(term, '')

        # If any letters remain, it contains algebraic variables
        return bool(re.search(r'[a-zA-Z]', expr_clean))


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

    def apply_trig_constraints(self):
        """
        Applies numeric constraints to sine and cosine variables
        when the corresponding angles have unique values.
        """
        import math
        from z3 import sat, unsat, Solver, Or

        # First, check if the solver is satisfiable
        if self.solver.check() != sat:
            print("Solver is unsatisfiable, cannot apply trig constraints")
            return 0

        # Get the current model
        model = self.solver.model()

        # Look for all sin_XXX and cos_XXX variables in self.variables
        trig_vars = []

        for var_name, var in self.variables.items():
            if var_name.startswith("sin_") or var_name.startswith("cos_"):
                parts = var_name.split("_", 1)
                if len(parts) == 2:
                    func, angle_name = parts
                    angle_var_name = f"angle_{angle_name}"

                    if angle_var_name in self.angles:
                        trig_vars.append({
                            "trig_var_name": var_name,
                            "angle_var_name": angle_var_name,
                            "angle_var": self.angles[angle_var_name],
                            "trig_var": self.variables[var_name],
                            "func": func,
                            "angle_name": angle_name
                        })

        if not trig_vars:
            return 0

        # For each trig variable, check if the angle has a unique value
        constraints_added = 0

        for data in trig_vars:
            angle_var = data["angle_var"]
            trig_var = data["trig_var"]
            func = data["func"]
            angle_name = data["angle_name"]
            trig_var_name = data["trig_var_name"]

            # Try to get the current angle value from the model
            try:
                angle_val_str = model.eval(angle_var).as_decimal(10)
                if angle_val_str.endswith('?'):
                    angle_val_str = angle_val_str[:-1]
                angle_val = float(angle_val_str)

                # Check if this angle value is uniquely determined
                temp_solver = Solver()
                for c in self.solver.assertions():
                    temp_solver.add(c)

                epsilon = 1e-6
                temp_solver.add(Or(
                    angle_var < angle_val - epsilon,
                    angle_var > angle_val + epsilon
                ))

                if temp_solver.check() == unsat:
                    # Calculate exact trig value based on special cases or general formula
                    if abs(angle_val - 90) < epsilon:
                        # 90 degrees
                        if func == "sin":
                            exact_trig_val = 1.0
                        else:  # cos
                            exact_trig_val = 0.0
                    elif abs(angle_val - 0) < epsilon:
                        # 0 degrees
                        if func == "sin":
                            exact_trig_val = 0.0
                        else:  # cos
                            exact_trig_val = 1.0
                    elif abs(angle_val - 180) < epsilon:
                        # 180 degrees
                        if func == "sin":
                            exact_trig_val = 0.0
                        else:  # cos
                            exact_trig_val = -1.0
                    elif abs(angle_val - 45) < epsilon or abs(angle_val - 135) < epsilon:
                        # 45 or 135 degrees
                        sqrt2_over_2 = math.sqrt(2) / 2
                        if func == "sin":
                            exact_trig_val = sqrt2_over_2
                        else:  # cos
                            exact_trig_val = sqrt2_over_2 if abs(angle_val - 45) < epsilon else -sqrt2_over_2
                    elif abs(angle_val - 30) < epsilon or abs(angle_val - 150) < epsilon:
                        # 30 or 150 degrees
                        if func == "sin":
                            exact_trig_val = 0.5
                        else:  # cos
                            exact_trig_val = math.sqrt(3) / 2 if abs(angle_val - 30) < epsilon else -math.sqrt(3) / 2
                    elif abs(angle_val - 60) < epsilon or abs(angle_val - 120) < epsilon:
                        # 60 or 120 degrees
                        if func == "sin":
                            exact_trig_val = math.sqrt(3) / 2
                        else:  # cos
                            exact_trig_val = 0.5 if abs(angle_val - 60) < epsilon else -0.5
                    else:
                        # General case
                        if func == "sin":
                            exact_trig_val = math.sin(math.radians(angle_val))
                        else:  # cos
                            exact_trig_val = math.cos(math.radians(angle_val))

                    # Round to help with numerical stability
                    exact_trig_val = round(exact_trig_val, 10)

                    # Check if the trig variable is already constrained to this value
                    trig_temp_solver = Solver()
                    for c in self.solver.assertions():
                        trig_temp_solver.add(c)

                    trig_temp_solver.add(Or(
                        trig_var < exact_trig_val - epsilon,
                        trig_var > exact_trig_val + epsilon
                    ))

                    if trig_temp_solver.check() == sat:
                        # Trig variable can have a different value, add constraint
                        self.solver.add(trig_var == exact_trig_val)
                        constraints_added += 1
                        print(f"Added constraint: {func}({angle_name}) = {exact_trig_val} (angle = {angle_val}°)")

            except Exception as e:
                print(f"Error processing angle {angle_name}: {e}")

        return constraints_added



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
            "congruent_triangle_property_angle_equal",
            "mirror_congruent_triangle_judgment_aas",
            "mirror_congruent_triangle_property_line_equal",
            "midsegment_of_triangle_judgment_midpoint",
            "midsegment_of_triangle_property_length",
            "parallel_judgment_par_par",
            "mirror_congruent_triangle_judgment_sas",
            "mirror_congruent_triangle_property_angle_equal",
            "arc_addition_measure",
            "diameter_of_circle_judgment_pass_centre",
            "isosceles_triangle_property_line_coincidence",
            "parallelogram_area_formula_sine",
            "midsegment_of_quadrilateral_property_length",
            "tangent_of_circle_property_length_equal",
            "quadrilateral_perimeter_formula",
            "congruent_triangle_judgment_aas",
            "similar_triangle_property_area_square_ratio",
            "congruent_arc_judgment_chord_equal",
            "congruent_arc_property_measure_equal",
            "equilateral_triangle_property_angle",
            "round_arc",
            "perpendicular_judgment_angle",
            "rectangle_judgment_right_angle",
            "circle_property_angle_of_osculation",
            "bisector_of_angle_judgment_angle_equal",
            "bisector_of_angle_property_line_ratio",
            "diameter_of_circle_judgment_right_angle",
            "mirror_similar_triangle_property_ratio",
            "mirror_congruent_triangle_judgment_sss"
        ]

        if theorem_name not in valid_theorems:
            return GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
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

        elif theorem_name == "bisector_of_angle_judgment_angle_equal":
            version = args[0]
            if version == "1":
                # Parse the conclusion to get the bisector and angle
                match = re.search(r'IsBisectorOfAngle\((\w+),(\w+)\)', conclusions[0])
                if not match:
                    return GeometricError(
                        tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                        message="Conclusion format error for bisector_of_angle_judgment_angle_equal",
                        details=f"Expected IsBisectorOfAngle(...) pattern but got {conclusions[0]}"
                    )

                bisector, angle_name = match.groups()  # e.g., "BD", "ABC"

                # Initialize angle_bisectors if it doesn't exist
                if not hasattr(self, "angle_bisectors"):
                    self.angle_bisectors = []

                # Add the angle bisector information
                self.angle_bisectors.append((bisector, angle_name))

                # Extract the key points
                vertex = angle_name[1]  # Middle letter is the vertex
                left_arm = angle_name[0]  # First letter of the original angle
                right_arm = angle_name[2]  # Last letter of the original angle
                bisector_point = bisector[1]  # Second letter of the bisector

                # Define the two sub-angles
                left_subangle = left_arm + vertex + bisector_point  # e.g., "ABD"
                right_subangle = bisector_point + vertex + right_arm  # e.g., "DBC"

                # Create angle variables for both sub-angles
                left_angle_var = self.add_angle(left_subangle[0], left_subangle[1], left_subangle[2])
                right_angle_var = self.add_angle(right_subangle[0], right_subangle[1], right_subangle[2])

                # Add the constraint that both angles are equal (definition of angle bisector)
                self.solver.add(left_angle_var == right_angle_var)

                print(f"Added angle bisector: {bisector} is a bisector of angle {angle_name}")
                print(f"Added constraint: angle {left_subangle} = angle {right_subangle}")
                return None
            else:
                return GeometricError(
                    tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,
                    message=f"Unsupported version {version} for bisector_of_angle_judgment_angle_equal",
                    details="Only version 1 is supported"
                )



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

                    return GeometricError(tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                                          message="Conclusion format error for angle_addition",

                                          details="Expected format: Equal(MeasureOfAngle(XXX),Add(MeasureOfAngle(YYY),MeasureOfAngle(ZZZ)))")

                return None
            else:
                return GeometricError(tier=ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION,

                                      message="these is no such version for the theorem",

                                      details="these is no such version for the theorem angle_addition")


        constraints_added = self.apply_trig_constraints()
        if constraints_added > 0:
            print(f"Added {constraints_added} trigonometric constraints after theorem {theorem_name}")

        return None  # or return the error if there was one


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


def verify_geometric_proof(filename: str, print_output=True) -> tuple:
    """
    Main function to verify a geometric proof.
    Returns (result, feedback, error_tier) where error_tier is one of:
    - "TIER1_THEOREM_CALL_SYNTAX_VIOLATION" for incorrect theorem calls
    - "TIER2_PREMISE_VIOLATION" for premise violations
    - "TIER3_GOAL_NOT_REACHED" for failures to reach the goal
    - None for successful verifications
    """
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

            # Extract error tier from feedback if there's a failure
            error_tier = None
            if not result and feedback:
                # Look for specific error tier mentions
                if "Error in TIER1_THEOREM_CALL_SYNTAX_VIOLATION" in feedback:
                    error_tier = ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION
                elif "Error in TIER2_PREMISE_VIOLATION" in feedback:
                    error_tier = ErrorTier.TIER2_PREMISE_VIOLATION
                elif "Error in TIER3_GOAL_NOT_REACHED" in feedback:
                    error_tier = ErrorTier.TIER3_GOAL_NOT_REACHED
                # Check for premise error patterns in detailed feedback
                elif feedback.startswith("verification failed.") and (
                        "Missing premise:" in feedback or "- You tried to use theorem:" in feedback):
                    error_tier = ErrorTier.TIER2_PREMISE_VIOLATION
                # Check for goal error patterns in detailed feedback
                elif feedback.startswith("verification failed.") and "- Goal:" in feedback:
                    error_tier = ErrorTier.TIER3_GOAL_NOT_REACHED
                # Default to TIER1 for other errors
                else:
                    error_tier = ErrorTier.TIER1_THEOREM_CALL_SYNTAX_VIOLATION

            print(f"\nOverall verification {'succeeded' if result else 'failed'}")
            return result, feedback, error_tier
        except Exception as e:
            print(f"Error: {str(e)}")
            return False, f"Error: {str(e)}", None


# Modified main section
if __name__ == "__main__":
    result, feedback, error_tier = verify_geometric_proof(
        "/Users/eitanstern/Desktop/orens_code/geometric_verifer/questions/the new format for questions after jan_17/new_45_questions/oren_random/1490_random",print_output=False)

    if not result:
        print(feedback)
    else:
        print("Verification succeeded")