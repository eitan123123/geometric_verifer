import os
from typing import List, Optional, Union
from typing import Union, Optional
from dataclasses import dataclass
import sympy as sp
from typing import List, Dict, Set, Optional, Union
# First, let's add an error class to handle different types of errors
from dataclasses import dataclass
from typing import Optional, List, Any
from enum import Enum





class ErrorTier(Enum):
    TIER1_THEOREM_CALL = 1    # Incorrect theorem call
    TIER2_PREMISE = 2         # Premise violation
    TIER3_GOAL_NOT_REACHED = 3  # Failed to reach goal

class ParserError(Exception):
    """Base class for parser errors"""
    def __init__(self, message: str, tier: int):
        self.message = message
        self.tier = tier
        super().__init__(self.message)

# -----------------------------
# Basic Structures
# -----------------------------

class Point:
    def __init__(self, name: str):
        self.name = name

    def __eq__(self, other):
        if not isinstance(other, Point):
            return False
        return self.name == other.name

    def __hash__(self):
        return hash(self.name)

    def __repr__(self):
        return f"{self.name}"

    def __str__(self):
        return self.name


class Line:
    def __init__(self, start_point: Point, end_point: Point):
        # Store points in canonical order (alphabetically) to ensure AB = BA
        if start_point.name <= end_point.name:
            self.startPoint = start_point
            self.endPoint = end_point
        else:
            self.startPoint = end_point
            self.endPoint = start_point

    def __eq__(self, other):
        if not isinstance(other, Line):
            return False
        # Only need to check one way since we store in canonical order
        return (self.startPoint == other.startPoint and
                self.endPoint == other.endPoint)

    def __hash__(self):
        # Hash based on canonical ordering
        return hash((self.startPoint.name, self.endPoint.name))

    def __repr__(self):
        return f"Line({self.startPoint}, {self.endPoint})"

    def __str__(self):
        return f"Line({self.startPoint}, {self.endPoint})"


class LengthStatement:
    def __init__(self, line: Line, length: float):
        self.line = line
        self.length = length

    def __repr__(self):
        return f"Length({self.line}) = {self.length}"

    def __str__(self):
        return f"Length({self.line}) = {self.length}"



@dataclass
class SymbolicExpression:
    """Represents a symbolic mathematical expression using sympy"""
    expr: sp.Expr

    def __add__(self, other):
        if isinstance(other, SymbolicExpression):
            return SymbolicExpression(self.expr + other.expr)
        return SymbolicExpression(self.expr + other)

    def __sub__(self, other):
        if isinstance(other, SymbolicExpression):
            return SymbolicExpression(self.expr - other.expr)
        return SymbolicExpression(self.expr - other)

    def __mul__(self, other):
        if isinstance(other, SymbolicExpression):
            return SymbolicExpression(self.expr * other.expr)
        return SymbolicExpression(self.expr * other)

    def __truediv__(self, other):
        if isinstance(other, SymbolicExpression):
            return SymbolicExpression(self.expr / other.expr)
        return SymbolicExpression(self.expr / other)
    @staticmethod
    def from_string(expr_str: str) -> 'SymbolicExpression':
        """Convert string expression to SymbolicExpression"""
        return SymbolicExpression(sp.sympify(expr_str))

    def evaluate(self, **substitutions) -> Optional[float]:
        """Evaluate expression with given variable values"""
        try:
            result = self.expr.subs(substitutions)
            if result.is_number:
                return float(result)
            return None
        except Exception:
            return None

    def __eq__(self, other):
        if isinstance(other, SymbolicExpression):
            return sp.simplify(self.expr - other.expr) == 0
        return False

    def __str__(self):
        return str(self.expr)
# -----------------------------
# Helper Constructor Functions
# --------------



class Angle:
    def __init__(self, p1: Point, v: Point, p2: Point):
        self.vertex = v
        self.point1 = p1
        self.point2 = p2

    def __eq__(self, other):
        if not isinstance(other, Angle):
            return False
        # Angle ABC = angle CBA, so check both orderings
        return (self.vertex == other.vertex and
                ((self.point1 == other.point1 and self.point2 == other.point2) or
                 (self.point1 == other.point2 and self.point2 == other.point1)))

    def __hash__(self):
        # Hash should be the same for ABC and CBA
        # Sort point names to ensure same hash for both orderings
        point_names = sorted([self.point1.name, self.point2.name])
        return hash((point_names[0], self.vertex.name, point_names[1]))

    def __repr__(self):
        return f"Angle({self.point1}, {self.vertex}, {self.point2})"

    def __str__(self):
        return f"Angle({self.point1}, {self.vertex}, {self.point2})"


class AngleStatement:
    """Associates an Angle with its measure which can be numeric or symbolic"""

    def __init__(self, angle: Angle,
                 measure: Union[float, str, SymbolicExpression, None]):
        self.angle = angle
        if measure is None:
            # Create a symbolic variable for an unknown angle measure
            # e.g. "_angle_ECD" for an angle ECD
            sym_name = f"_angle_{angle.point1.name}{angle.vertex.name}{angle.point2.name}"
            self.measure = SymbolicExpression(sp.Symbol(sym_name))

        elif isinstance(measure, (int, float)):
            self.measure = SymbolicExpression(sp.Number(float(measure)))
        elif isinstance(measure, str):
            self.measure = SymbolicExpression.from_string(measure)
        elif isinstance(measure, SymbolicExpression):
            self.measure = measure
        else:
            raise ValueError(f"Unsupported measure type: {type(measure)}")

    def __repr__(self):
        return f"Measure({self.angle}) = {self.measure}"

    def __str__(self):
        return f"Measure({self.angle}) = {self.measure}"


def normalize_polygon_points(points: List[Point]) -> List[Point]:
    """
    Normalize polygon points to canonical form:
    - For triangles: Start with smallest point name and maintain orientation
    - For higher polygons: Start with smallest point name and maintain order
    """
    if len(points) <= 2:
        return points

    # Find index of point with smallest name
    min_idx = min(range(len(points)), key=lambda i: points[i].name)

    # For triangles, we can rotate to any orientation
    if len(points) == 3:
        rotated = points[min_idx:] + points[:min_idx]
        # Check both orientations and take the one that gives lexicographically
        # smaller sequence of point names
        reversed_rotated = [rotated[0]] + list(reversed(rotated[1:]))
        names_normal = [p.name for p in rotated]
        names_reversed = [p.name for p in reversed_rotated]
        return reversed_rotated if names_reversed < names_normal else rotated

    # For higher polygons, maintain order but start from smallest point
    return points[min_idx:] + points[:min_idx]
class EquationSystem:
    """Manages a system of geometric equations"""

    def __init__(self):
        self.equations: List[sp.Equation] = []
        self.variables: Set[sp.Symbol] = set()

    def add_equation(self, expr1: SymbolicExpression, expr2: SymbolicExpression):
        """Add equation expr1 = expr2 to the system"""
        try:
            eq = sp.Eq(expr1.expr, expr2.expr)
            if eq not in self.equations:  # Avoid duplicate equations
                self.equations.append(eq)
                self.variables.update(eq.free_symbols)
        except RecursionError:
            print("Warning: RecursionError in equation handling")

    def solve(self) -> Dict[str, float]:
        """Solve the system of equations"""
        try:
            solution = sp.solve(self.equations, list(self.variables))
            if isinstance(solution, dict):
                return {str(var): float(val)
                        for var, val in solution.items()}
            elif isinstance(solution, list) and len(solution) == 1:
                return {str(var): float(val)
                        for var, val in solution[0].items()}
            return {}
        except Exception:
            return {}

def makePoint(n: str) -> Point:
    return Point(n)


def makeLine(p1: Point, p2: Point) -> Line:
    return Line(p1, p2)


def makeAngle(p1: Point, v: Point, p2: Point) -> Angle:
    return Angle(p1, v, p2)


# -----------------------------
# Complex Geometric Structures
# -----------------------------

class GeometricFact:
    def __init__(
            self,
            type_: str,
            points: List[Point] = None,
            lines: List[Line] = None,
            angles: List[Angle] = None,
            value: Optional[float] = None,
            related_facts: List[str] = None
    ):
        self.type = type_

        # Handle points based on fact type
        if points:
            if self.type == "Collinear":
                # For collinear points, any order is valid
                self.points = sorted(points, key=lambda p: p.name)
            elif self.type in ["Triangle", "Shape", "Parallelogram"]:
                # For shapes, normalize to start with smallest point name
                min_idx = min(range(len(points)), key=lambda i: points[i].name)
                self.points = points[min_idx:] + points[:min_idx]
            else:
                self.points = points
        else:
            self.points = []

        # Handle lines (order doesn't matter for pairs)
        if lines and len(lines) == 2 and self.type in ["Parallel", "Perpendicular"]:
            self.lines = sorted(lines, key=lambda l: (l.startPoint.name, l.endPoint.name))
        else:
            self.lines = lines if lines else []

        # Handle angles
        if angles and self.type == "AngleEqual":
            self.angles = sorted(angles, key=lambda a: (a.vertex.name, min(a.point1.name, a.point2.name)))
        else:
            self.angles = angles if angles else []

        self.value = value
        self.relatedFacts = related_facts if related_facts else []

    def __eq__(self, other):
        if not isinstance(other, GeometricFact):
            return False
        if self.type != other.type:
            return False

        # Special handling based on fact type
        if self.type == "Collinear":
            # Order doesn't matter for collinear points
            return set(self.points) == set(other.points)

        elif self.type in ["Shape", "Parallelogram"]:
            # Consider cyclic rotations only for shapes with > 3 points
            return points_equal_with_rotations(self.points, other.points)

        elif self.type == "Triangle":
            # For triangles, consider both rotations and reversals
            return points_equal_with_rotations(self.points, other.points)

        elif self.type in ["Parallel", "Perpendicular"]:
            # Order of lines doesn't matter
            return set(self.lines) == set(other.lines)

        elif self.type == "AngleEqual":
            # Order of angles doesn't matter
            return set(self.angles) == set(other.angles)

        # For other types, compare directly
        return (self.points == other.points and
                self.lines == other.lines and
                self.angles == other.angles and
                self.value == other.value)

    def __hash__(self):
        if self.type == "Collinear":
            return hash((self.type, frozenset(p.name for p in self.points)))
        elif self.type in ["Shape", "Parallelogram", "Triangle"]:
            # Hash based on canonical form (starting with smallest point name)
            min_idx = min(range(len(self.points)), key=lambda i: self.points[i].name)
            canonical_points = self.points[min_idx:] + self.points[:min_idx]
            return hash((self.type, tuple(p.name for p in canonical_points)))
        elif self.type == "AngleEqual":
            return hash((self.type, frozenset((a.vertex.name,
                                               frozenset([a.point1.name, a.point2.name])) for a in self.angles)))
        else:
            return hash((self.type,
                         tuple(p.name for p in self.points),
                         tuple((l.startPoint.name, l.endPoint.name) for l in self.lines),
                         tuple((a.vertex.name, a.point1.name, a.point2.name)
                               for a in self.angles),
                         self.value))

    def __str__(self):
        if self.type == "Collinear":
            pts = ",".join(str(p) for p in self.points)
            return f"Collinear({pts})"
        elif self.type in ["Shape", "Parallelogram", "Triangle"]:
            pts = ",".join(str(p) for p in self.points)
            return f"{self.type}({pts})"
        elif self.type == "Parallel":
            lns = ",".join(str(l) for l in self.lines)
            return f"Parallel({lns})"
        elif self.type == "AngleEqual":
            angs = ",".join(str(a) for a in self.angles)
            return f"AngleEqual({angs})"
        else:
            return f"{self.type}({','.join(str(p) for p in self.points)})"


class GeometricState:
    """Enhanced GeometricState with equation handling"""

    def __init__(self, facts: List[GeometricFact],
                 lengths: List[LengthStatement] = None,
                 angles: List[AngleStatement] = None):
        self.facts = facts if facts else []
        self.lengths = lengths if lengths else []
        self.angles = angles if angles else []
        self.equations = EquationSystem()

    def add_angle_equality(self, angle1: AngleStatement, angle2: AngleStatement):
        """Add equation from angle equality"""
        self.equations.add_equation(angle1.measure, angle2.measure)

    def solve_equations(self) -> None:
        """Solve current equation system and update angle measures"""
        solutions = self.equations.solve()
        if not solutions:
            return

        # Update angle measures with solved values
        for angle_stmt in self.angles:
            evaluated = angle_stmt.measure.evaluate(**solutions)
            if evaluated is not None:
                angle_stmt.measure = SymbolicExpression(sp.Number(evaluated))


class TheoremRequirement:
    """
    A single piece of data (requirement) needed to apply a theorem:
      type: e.g. "collinear", "parallel", "angle_measure"
      points: the points relevant to the requirement
      lines: the lines relevant to the requirement
      angles: the angles relevant to the requirement
      value: optional numeric value (e.g. angle measure)
    """

    def __init__(
            self,
            type_: str,
            points: List[Point] = None,
            lines: List[Line] = None,
            angles: List[Angle] = None,
            value: Optional[float] = None
    ):
        self.type = type_
        self.points = points if points else []
        self.lines = lines if lines else []
        self.angles = angles if angles else []
        self.value = value

    def __repr__(self):
        return (f"TheoremRequirement(type={self.type}, "
                f"points={self.points}, lines={self.lines}, angles={self.angles}, value={self.value})")


class TheoremConclusion:
    """
    What a theorem concludes if the requirements are met.
    """

    def __init__(
            self,
            type_: str,
            points: List[Point] = None,
            lines: List[Line] = None,
            angles: List[Angle] = None,
            value: Optional[float] = None,
            related_facts: List[str] = None
    ):
        self.type = type_
        self.points = points if points else []
        self.lines = lines if lines else []
        self.angles = angles if angles else []
        self.value = value
        self.relatedFacts = related_facts if related_facts else []

    def __repr__(self):
        return (f"TheoremConclusion(type={self.type}, points={self.points}, "
                f"lines={self.lines}, angles={self.angles}, "
                f"value={self.value}, relatedFacts={self.relatedFacts})")


class TheoremRule:
    """
    Defines a theorem's name, the list of requirements, and the list of conclusions.
    """

    def __init__(self, name: str,
                 requirements: List[TheoremRequirement],
                 conclusions: List[TheoremConclusion]):
        self.name = name
        self.requirements = requirements
        self.conclusions = conclusions

    def __repr__(self):
        return f"TheoremRule(name={self.name})"



@dataclass
class GeometricError:
    tier: ErrorTier
    message: str
    details: Optional[str] = None
    related_objects: Optional[List[Any]] = None


# -----------------------------
# Adjacent Angles Helper
# -----------------------------

def areAdjacent(angle1: Angle, angle2: Angle) -> bool:
    """
    Check if two angles share the same vertex and share exactly one ray.
    Updated to handle canonical angle representations.
    """
    if angle1.vertex != angle2.vertex:
        return False

    # Get all points in both angles (excluding vertex)
    points1 = {angle1.point1, angle1.point2}
    points2 = {angle2.point1, angle2.point2}

    # They should share exactly one point (besides the vertex)
    common_points = points1.intersection(points2)
    return len(common_points) == 1


# -----------------------------
# Theorem Definitions
# -----------------------------

angleAdditionTheorem = TheoremRule(
    name="angle_addition",
    requirements=[
        TheoremRequirement(type_="angle_measure"),  # BCE measure
        TheoremRequirement(type_="angle_measure"),  # DCB measure
        TheoremRequirement(type_="adjacent_angles")  # BCE and DCB adjacency
    ],
    conclusions=[
        TheoremConclusion(type_="angle_sum", related_facts=["angle_addition"])
    ]
)




parallelogramOppositeAngleTheorem = TheoremRule(
    name="parallelogram_property_opposite_angle_equal",
    requirements=[
        TheoremRequirement(type_="parallelogram", points=[])  # Will be filled with parallelogram points
    ],
    conclusions=[
        TheoremConclusion(type_="angle_equal", related_facts=["parallelogram_angles"])
    ]
)




parallelAlternateInteriorTheorem = TheoremRule(
    name="parallel_property_alternate_interior_angle",
    requirements=[
        TheoremRequirement(type_="parallel")
    ],
    conclusions=[
        TheoremConclusion(type_="angle_equal"),
        TheoremConclusion(type_="angle_measure")  # Typically to copy from known angle
    ]
)

adjacentComplementaryAngleTheorem = TheoremRule(
    name="adjacent_complementary_angle",
    requirements=[
        TheoremRequirement(type_="collinear"),  # Points for the line
        TheoremRequirement(type_="angle_measure")  # The angle we know
    ],
    conclusions=[
        TheoremConclusion(
            type_="angle_measure",
            related_facts=["complementary_angles"]
        )
    ]
)

parallelAlternateInteriorAnglesTheorem = TheoremRule(
    name="parallel_property_alternate_interior_angle",
    requirements=[
        TheoremRequirement(type_="parallel")
    ],
    conclusions=[
        TheoremConclusion(type_="angle_equal", related_facts=["parallel_angles"]),
        TheoremConclusion(type_="angle_measure")  # Add this to copy the measure
    ]
)



quadrilateralAngleSumTheorem = TheoremRule(
    name="quadrilateral_property_angle_sum",
    requirements=[
        TheoremRequirement(type_="shape", points=[])  # Will be filled with quad points
    ],
    conclusions=[
        TheoremConclusion(
            type_="angle_sum",
            angles=[],  # Will be filled with all 4 angles
            related_facts=["quadrilateral_angles_360"]
        )
    ]
)

# -----------------------------
# Filling Requirements/Conclusions
# -----------------------------

def fillRequirements(reqs: List[TheoremRequirement],
                     points: List[Point],
                     lines: List[Line],
                     angles: List[Angle],
                     state: GeometricState) -> List[TheoremRequirement]:
    """
    Attempts to place the relevant points/lines/angles into each requirement
    if they are not already specified.
    """
    filled = []
    for i, req in enumerate(reqs):
        new_req = TheoremRequirement(
            type_=req.type,
            points=req.points if req.points else points,
            lines=req.lines if req.lines else lines,
            angles=req.angles if req.angles else angles,
            value=req.value
        )

        # Specific logic for some requirement types:
        if req.type == "adjacent_angles":
            if len(angles) >= 2:
                new_req.angles = [angles[0], angles[1]]

        elif req.type == "angle_measure":
            # For adjacent_complementary_angle theorem
            if len(angles) == 2:  # If we're given exactly two angles
                if i == 1:  # Second requirement is for the known angle
                    known_angle = next((ang for ang in angles if any(
                        x.angle == ang for x in state.angles)), None)
                    if known_angle:
                        new_req.angles = [known_angle]
                else:  # First requirement is for the angle we want to find
                    unknown_angle = next((ang for ang in angles if not any(
                        x.angle == ang for x in state.angles)), None)
                    if unknown_angle:
                        new_req.angles = [unknown_angle]
            # Default case from original code
            elif len(angles) >= 3:
                if i == 0:
                    new_req.angles = [angles[1]]
                elif i == 1:
                    new_req.angles = [angles[2]]
                else:
                    new_req.angles = [angles[0]]
            elif len(angles) == 1:
                new_req.angles = [angles[0]]

        filled.append(new_req)
    return filled


def fillConclusions(concls: List[TheoremConclusion],
                    points: List[Point],
                    lines: List[Line],
                    angles: List[Angle]) -> List[TheoremConclusion]:
    """
    Similarly, fill in the angles/points/lines for the conclusions if needed.
    """
    filled = []
    for concl in concls:
        new_concl = TheoremConclusion(
            type_=concl.type,
            points=concl.points if concl.points else points,
            lines=concl.lines if concl.lines else lines,
            angles=concl.angles if concl.angles else angles,
            value=concl.value,
            related_facts=concl.relatedFacts
        )

        # "angle_sum" with quadrilateral_angles_360
        if (concl.type == "angle_sum" and
            "quadrilateral_angles_360" in concl.relatedFacts):
            if len(angles) >= 4:
                new_concl.angles = angles[:4]  # Take all 4 angles

        # Regular "angle_sum" special logic
        elif concl.type == "angle_sum":
            if len(angles) >= 3:
                new_concl.angles = [angles[0], angles[1], angles[2]]

        # "angle_measure" with "complementary_angles"
        if concl.type == "angle_measure" and "complementary_angles" in concl.relatedFacts:
            if len(angles) >= 2:
                # The first angle should be the one we want to find
                new_concl.angles = [angles[0]]

        filled.append(new_concl)
    return filled


# -----------------------------
# Angle Propagation (Equality)
# -----------------------------

def propagateEqualAnglesHelper(state: GeometricState) -> Optional[GeometricState]:
    changed_something = False
    new_angles = list(state.angles)

    for fact in state.facts:
        if fact.type == "AngleEqual" and len(fact.angles) == 2:
            angle1, angle2 = fact.angles
            measure1 = next((x for x in new_angles if x.angle == angle1), None)
            measure2 = next((x for x in new_angles if x.angle == angle2), None)

            if measure1 and measure2:
                # Add equation to the system
                state.add_angle_equality(measure1, measure2)
                changed_something = True
                # Solve the system
                state.solve_equations()

    if changed_something:
        return GeometricState(facts=state.facts, lengths=state.lengths, angles=new_angles)
    else:
        return None

def propagateEqualAngles(state: GeometricState, size: int = 100) -> GeometricState:
    """Repeatedly propagate angle equalities and solve equations"""
    current_state = state
    for _ in range(size):
        new_state = propagateEqualAnglesHelper(current_state)
        if new_state is None:
            return current_state
        current_state = new_state
    return current_state


# -----------------------------
# Apply Conclusions to State
# -----------------------------


def get_opposite_angles_in_parallelogram(points: List[Point]) -> List[tuple[Angle, Angle]]:
    """
    Given points [A,B,C,D] of a parallelogram in order,
    returns pairs of opposite angles:
    - ∠DAB opposite to ∠BCD
    - ∠ABC opposite to ∠CDA
    """
    if len(points) != 4:
        return []

    A, B, C, D = points
    angle1 = makeAngle(D, A, B)
    opposite1 = makeAngle(B, C, D)
    angle2 = makeAngle(A, B, C)
    opposite2 = makeAngle(C, D, A)

    return [(angle1, opposite1), (angle2, opposite2)]


def checkParallelogramOppositeAngles(state: GeometricState, req: TheoremRequirement) -> tuple[
    bool, Optional[GeometricError]]:
    """Check if the given angles are actually opposite in the parallelogram"""

    # Find the parallelogram fact
    parallelogram_fact = next(
        (f for f in state.facts
         if f.type == "Parallelogram" and set(f.points) == set(req.points)),
        None
    )

    if not parallelogram_fact:
        return False, GeometricError(
            tier=ErrorTier.TIER2_PREMISE,
            message=f"No parallelogram found with points {[p.name for p in req.points]}"
        )

    # Get valid opposite angle pairs for this parallelogram
    valid_pairs = get_opposite_angles_in_parallelogram(parallelogram_fact.points)

    # Check if the angles we're trying to equate are actually opposite
    target_angles = set(req.angles)
    if not any(target_angles == set(pair) for pair in valid_pairs):
        return False, GeometricError(
            tier=ErrorTier.TIER2_PREMISE,
            message=f"Angles {[str(a) for a in req.angles]} are not opposite angles in parallelogram {[p.name for p in parallelogram_fact.points]}",
            details="Valid opposite pairs:\n" + "\n".join(f"- {a1} opposite {a2}" for a1, a2 in valid_pairs)
        )

    return True, None


def get_cyclic_rotations(points: List[Point]) -> List[List[Point]]:
    """Get all cyclic rotations of a list of points."""
    n = len(points)
    rotations = []
    for i in range(n):
        rotation = points[i:] + points[:i]
        rotations.append(rotation)
    return rotations


def points_equal_with_rotations(points1: List[Point], points2: List[Point], fact_type: str) -> bool:
    """
    Check if two point sequences are equal based on the geometric fact type.
    - Triangles: consider both rotations and reversals
    - General Shapes: only consider cyclic rotations
    - Parallelograms: must match exactly (order matters)
    """
    if len(points1) != len(points2):
        return False

    if fact_type == "Triangle":  # Triangle case: consider rotations and reversals
        rotations = get_cyclic_rotations(points1)
        rotations.extend(get_cyclic_rotations(list(reversed(points1))))
        return points2 in rotations
    elif fact_type == "Parallelogram":  # Parallelogram case: order matters
        return points1 == points2
    elif fact_type == "Shape":  # General shape case: consider cyclic rotations
        rotations = get_cyclic_rotations(points1)
        return points2 in rotations
    else:  # Default case
        return points1 == points2



def applyConclusion(state: GeometricState, concl: TheoremConclusion) -> GeometricState:
    """
    Modify the state based on the conclusion type.
    """
    new_facts = list(state.facts)
    new_angles = list(state.angles)

    # angle_sum with quadrilateral_angles_360
    if (concl.type == "angle_sum" and
            "quadrilateral_angles_360" in concl.relatedFacts):
        if len(concl.angles) >= 4:
            angles_in_state = [
                x for x in new_angles
                if x.angle in concl.angles[:4]
            ]
            if len(angles_in_state) == 4:
                # Create equation: a1 + a2 + a3 + a4 = 360
                expr_sum = "+".join(f"({x.measure.expr})" for x in angles_in_state)
                state.equations.add_equation(
                    SymbolicExpression.from_string(expr_sum),
                    SymbolicExpression.from_string("360")
                )
                state.solve_equations()
                return state
        return state

    # angle_measure
    if concl.type == "angle_measure":
        if len(concl.angles) == 1:
            targetAngle = concl.angles[0]

            # angle_addition
            if "angle_addition" in concl.relatedFacts:
                relevant = [x for x in new_angles if areAdjacent(x.angle, targetAngle)]
                if not relevant:
                    return state
                total = sum(x.measure for x in relevant)
                new_angles = [x for x in new_angles if x.angle != targetAngle]
                new_angles.append(AngleStatement(angle=targetAngle, measure=total))
                return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)

            # complementary_angles (old logic if exactly 1 angle is concluded)
            elif "complementary_angles" in concl.relatedFacts:
                if len(concl.angles) == 1:
                    known = next((x for x in new_angles if x.angle != targetAngle
                                  and x.angle.vertex == targetAngle.vertex), None)
                    if known:
                        import sympy as sp
                        comp_val = SymbolicExpression(sp.Number(180.0) - known.measure.expr)
                        new_angles = [x for x in new_angles if x.angle != targetAngle]
                        new_angles.append(AngleStatement(angle=targetAngle, measure=comp_val))
                        return GeometricState(facts=new_facts, lengths=state.lengths,
                                              angles=new_angles)

            # parallel_angles
            elif "parallel_angles" in concl.relatedFacts:
                source_measure = None
                for x in new_angles:
                    if x.angle != targetAngle:
                        has_equality = any(
                            f for f in state.facts
                            if f.type == "AngleEqual" and
                            x.angle in f.angles and
                            targetAngle in f.angles
                        )
                        if has_equality:
                            source_measure = x
                            break
                if source_measure:
                    new_angles = [z for z in new_angles if z.angle != targetAngle]
                    new_angles.append(AngleStatement(angle=targetAngle,
                                                     measure=source_measure.measure))
                    return GeometricState(facts=new_facts, lengths=state.lengths,
                                          angles=new_angles)

            # angle_subtraction
            elif "angle_subtraction" in concl.relatedFacts:
                relevant = [x for x in new_angles if areAdjacent(x.angle, targetAngle)]
                if not relevant:
                    return state
                largest = max(relevant, key=lambda x: x.measure)
                other = next((x for x in relevant if x != largest), None)
                if not other:
                    return state
                diff_val = largest.measure - other.measure
                new_angles = [x for x in new_angles if x.angle != targetAngle]
                new_angles.append(AngleStatement(angle=targetAngle, measure=diff_val))
                return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)

            else:
                # fallback: if the angle is already known, just re-add it
                existing = next((x for x in new_angles if x.angle == targetAngle), None)
                if not existing:
                    return state
                new_angles = [x for x in new_angles if x.angle != targetAngle]
                new_angles.append(AngleStatement(angle=targetAngle, measure=existing.measure))
                return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)

        # -------------------- PATCH for 2-angle complementary --------------------
        elif "complementary_angles" in concl.relatedFacts and len(concl.angles) == 2:
            a1, a2 = concl.angles
            measure1 = next((x for x in new_angles if x.angle == a1), None)
            measure2 = next((x for x in new_angles if x.angle == a2), None)

            val1 = measure1.measure.evaluate() if measure1 else None
            val2 = measure2.measure.evaluate() if measure2 else None

            # If exactly one is known => set the other to 180 - known
            if val1 is not None and val2 is None:
                new_val = SymbolicExpression.from_string(str(180.0 - val1))
                new_angles.remove(measure2)
                new_angles.append(AngleStatement(a2, new_val))

            elif val2 is not None and val1 is None:
                new_val = SymbolicExpression.from_string(str(180.0 - val2))
                new_angles.remove(measure1)
                new_angles.append(AngleStatement(a1, new_val))

            return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)

        # -------------------------------------------------------------------------

        return state

    # angle_equal
    elif concl.type == "angle_equal":
        if len(concl.angles) == 2:
            a1, a2 = concl.angles
            # Add the equality fact
            new_fact = GeometricFact(type_="AngleEqual", angles=[a1, a2],
                                     related_facts=["angle_equal"])
            new_facts.append(new_fact)

            # Propagate measure if the other angle is known
            measure1 = next((x for x in new_angles if x.angle == a1), None)
            measure2 = next((x for x in new_angles if x.angle == a2), None)

            if measure1 and not measure2:
                new_angles.append(AngleStatement(angle=a2, measure=measure1.measure))
            elif measure2 and not measure1:
                new_angles.append(AngleStatement(angle=a1, measure=measure2.measure))

            return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)
        return state

    # angle_sum
    elif concl.type == "angle_sum":
        if len(concl.angles) == 3:
            resultA, angle1, angle2 = concl.angles[0], concl.angles[1], concl.angles[2]
            m1 = next((x for x in new_angles if x.angle == angle1), None)
            m2 = next((x for x in new_angles if x.angle == angle2), None)
            if m1 and m2:
                new_val = SymbolicExpression(m1.measure.expr + m2.measure.expr)
                new_angles = [x for x in new_angles if x.angle != resultA]
                new_angles.append(AngleStatement(angle=resultA, measure=new_val))
                return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)
        return state

    # Default: no changes
    return state


def applyConclusions(state: GeometricState, concls: List[TheoremConclusion]) -> GeometricState:
    """
    Applies each conclusion to the state in order.
    """
    currentState = state
    for concl in concls:
        currentState = applyConclusion(currentState, concl)
    return currentState


# -----------------------------
# Checking Requirements
# -----------------------------

def checkRequirementWithDetailedError(state: GeometricState, req: TheoremRequirement) -> tuple[
    bool, Optional[GeometricError]]:
    """Enhanced version of checkRequirementWithDebug that returns structured errors"""

    if req.type == "shape":
        needed_points = set(req.points)
        found_fact = None
        for fact in state.facts:
            if fact.type == "Shape":
                fact_points = set(fact.points)
                if fact_points == needed_points:
                    found_fact = fact
                    break
        if not found_fact:
            shape_facts = [f for f in state.facts if f.type == "Shape"]
            error = GeometricError(
                tier=ErrorTier.TIER2_PREMISE,
                message=f"Shape with points {[p.name for p in req.points]} not found",
                details=f"Available shapes: {[f.points for f in shape_facts]}",
                related_objects=req.points
            )
            return False, error
        return True, None

    elif req.type == "collinear":
        needed = set(req.points)
        found_fact = None
        for fact in state.facts:
            if fact.type == "Collinear":
                fact_points = set(fact.points)
                if needed.issubset(fact_points):
                    found_fact = fact
                    break
        if not found_fact:
            collinear_facts = [f for f in state.facts if f.type == "Collinear"]
            error = GeometricError(
                tier=ErrorTier.TIER2_PREMISE,
                message=f"Points {[p.name for p in req.points]} not proven collinear",
                details=f"Known collinear points: {[f.points for f in collinear_facts]}",
                related_objects=req.points
            )
            return False, error
        return True, None

    elif req.type == "angle_measure":
        if len(req.angles) == 1:
            angle = req.angles[0]
            measure = next((x for x in state.angles if x.angle == angle), None)
            if not measure:
                known_angles = [x.angle for x in state.angles]
                error = GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"No measure found for required angle {angle}",
                    details=f"Known angle measurements: {known_angles}",
                    related_objects=[angle]
                )
                return False, error
            return True, None
        elif len(req.angles) == 2:
            angle1, angle2 = req.angles
            measure1 = next((x for x in state.angles if x.angle == angle1), None)
            measure2 = next((x for x in state.angles if x.angle == angle2), None)
            if not measure1 or not measure2:
                known_angles = [x.angle for x in state.angles]
                missing = []
                if not measure1:
                    missing.append(angle1)
                if not measure2:
                    missing.append(angle2)
                error = GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Missing measures for angles: {missing}",
                    details=f"Known angle measurements: {known_angles}",
                    related_objects=missing
                )
                return False, error
            return True, None
        return True, None

    elif req.type == "parallelogram":
        needed_points = req.points  # Keep as list to maintain order
        found_fact = None
        for fact in state.facts:
            if fact.type == "Parallelogram":
                # Check exact match or cyclic rotations
                if fact.points == needed_points:
                    found_fact = fact
                    break

        if not found_fact:
            error = GeometricError(
                tier=ErrorTier.TIER2_PREMISE,
                message=f"Points {[p.name for p in req.points]} do not form a known parallelogram",
                related_objects=req.points
            )
            return False, error

        # Additional check for opposite angles when applying parallelogram theorem
        if len(req.angles) == 2:
            valid_pairs = get_opposite_angles_in_parallelogram(found_fact.points)
            target_angles = set(req.angles)
            if not any(target_angles == set(pair) for pair in valid_pairs):
                error = GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Angles {[str(a) for a in req.angles]} are not opposite angles in parallelogram {[p.name for p in found_fact.points]}",
                    details="Valid opposite pairs:\n" + "\n".join(f"- {a1} opposite {a2}" for a1, a2 in valid_pairs),
                    related_objects=req.angles
                )
                return False, error

        return True, None

    elif req.type == "parallel":
        needed = req.lines
        found_fact = None
        for fact in state.facts:
            if fact.type == "Parallel":
                if fact.lines == needed or fact.lines[::-1] == needed:
                    found_fact = fact
                    break
        if not found_fact:
            error = GeometricError(
                tier=ErrorTier.TIER2_PREMISE,
                message=f"Lines {needed} not proven parallel",
                related_objects=needed
            )
            return False, error
        return True, None

    elif req.type == "adjacent_angles":
        if len(req.angles) == 2:
            angle1, angle2 = req.angles
            same_vertex = (angle1.vertex == angle2.vertex)
            share_ray = (
                    angle1.point1 == angle2.point1 or
                    angle1.point2 == angle2.point1 or
                    angle1.point1 == angle2.point2 or
                    angle1.point2 == angle2.point2
            )
            if not (same_vertex and share_ray):
                error = GeometricError(
                    tier=ErrorTier.TIER2_PREMISE,
                    message=f"Angles {angle1} and {angle2} are not adjacent",
                    details=f"Same vertex: {same_vertex}, Share ray: {share_ray}",
                    related_objects=[angle1, angle2]
                )
                return False, error
            return True, None
        else:
            error = GeometricError(
                tier=ErrorTier.TIER1_THEOREM_CALL,
                message="Invalid number of angles for adjacency check",
                related_objects=req.angles
            )
            return False, error

    error = GeometricError(
        tier=ErrorTier.TIER1_THEOREM_CALL,
        message=f"Unrecognized requirement type: {req.type}"
    )
    return False, error


def formatError(error: GeometricError) -> str:
    """Formats a GeometricError into a human-readable message"""
    if error.tier == ErrorTier.TIER1_THEOREM_CALL:
        header = "Error in Tier 1: Incorrect theorem call"
    else:
        header = "Error in Tier 2: Premise violation"

    message = f"\n{header}\n{'=' * len(header)}\n"
    message += f"• {error.message}\n"

    if error.details:
        message += f"Additional details:\n{error.details}\n"

    if error.related_objects:
        message += "Related objects:\n"
        for obj in error.related_objects:
            message += f"  - {obj}\n"

    return message
# -----------------------------
# Main Theorem Application
# -----------------------------

def applyGeometricTheoremWithErrors(
        rule: TheoremRule,
        state: GeometricState,
        points: List[Point],
        lines: List[Line],
        angles: List[Angle]
) -> tuple[Optional[GeometricState], Optional[GeometricError]]:
    """Enhanced version of applyGeometricTheoremWithDebug that returns structured errors"""

    # Validate theorem call structure
    if not rule.requirements:
        return None, GeometricError(
            tier=ErrorTier.TIER1_THEOREM_CALL,
            message=f"Theorem {rule.name} has no requirements defined"
        )

    # Fill requirements and validate
    try:
        filled_requirements = fillRequirements(rule.requirements, points, lines, angles, state)
        filled_conclusions = fillConclusions(rule.conclusions, points, lines, angles)
    except Exception as e:
        return None, GeometricError(
            tier=ErrorTier.TIER1_THEOREM_CALL,
            message=f"Failed to fill theorem requirements/conclusions: {str(e)}"
        )

    # Check each requirement
    for req in filled_requirements:
        met, error = checkRequirementWithDetailedError(state, req)
        if not met:
            return None, error

    # Apply conclusions
    try:
        resultState = applyConclusions(state, filled_conclusions)
        return resultState, None
    except Exception as e:
        return None, GeometricError(
            tier=ErrorTier.TIER1_THEOREM_CALL,
            message=f"Failed to apply conclusions: {str(e)}"
        )


# -----------------------------
# File writing
# -----------------------------




# -----------------------------
# Main Function
# -----------------------------

def verify_q1():
    X = makePoint("X")
    W = makePoint("W")
    Z = makePoint("Z")
    Y = makePoint("Y")

    angleWZY = makeAngle(W, Z, Y)
    angleXWZ = makeAngle(X, W, Z)
    angleYXW = makeAngle(Y, X, W)
    angleZYX = makeAngle(Z, Y, X)

    initial_facts = [
        GeometricFact(type_="Shape", points=[X, W, Z, Y])
    ]
    initial_angles = [
        AngleStatement(angleWZY, "a + 2"),
        AngleStatement(angleXWZ, "a/2 + 8"),
        AngleStatement(angleYXW, "a"),
        AngleStatement(angleZYX, "a - 28")
    ]

    initialState = GeometricState(facts=initial_facts, angles=initial_angles)
    print("Initial State:")
    print("=============")
    for fact in initialState.facts:
        print(f"• {fact}")
    for angle in initialState.angles:
        print(f"• {angle}")
    print()

    result1, error = applyGeometricTheoremWithErrors(
        quadrilateralAngleSumTheorem,
        initialState,
        [X, W, Z, Y],
        [],
        [angleWZY, angleXWZ, angleYXW, angleZYX]
    )

    if error:
        print(formatError(error))
        return

    finalState = propagateEqualAngles(result1)
    finalAngleZYX = next((x for x in finalState.angles if x.angle == angleZYX), None)
    if finalAngleZYX:
        value = finalAngleZYX.measure.evaluate()
        if value is not None:
            print(f"Final Result:")
            print(f"============")
            print(f"∠ZYX = {value}° (Expected: 80°)")
            print(f"Verification: {'✓ Successful' if abs(value - 80) < 1e-10 else '✗ Failed'}")

def verify_q2():
    A = makePoint("A")
    B = makePoint("B")
    C = makePoint("C")
    D = makePoint("D")
    E = makePoint("E")

    angleBCD = makeAngle(D, C, B)
    angleDCE = makeAngle(D, C, E)
    angleDAB = makeAngle(D, A, B)

    initial_facts = [
        GeometricFact(type_="Collinear", points=[B, C, E]),
        GeometricFact(type_="Parallelogram", points=[A, B, C, D])
    ]
    initial_angles = [
        AngleStatement(angleDCE, 70.0)
    ]

    initialState = GeometricState(facts=initial_facts, angles=initial_angles)
    print("Initial State:")
    print("=============")
    for fact in initialState.facts:
        print(f"• {fact}")
    for angle in initialState.angles:
        print(f"• {angle}")
    print()

    result1, error = applyGeometricTheoremWithErrors(
        adjacentComplementaryAngleTheorem,
        initialState,
        [B, C, E],
        [],
        [angleBCD, angleDCE]
    )

    if error:
        print(formatError(error))
        return

    state1WithPropagation = propagateEqualAngles(result1)

    result2, error = applyGeometricTheoremWithErrors(
        parallelogramOppositeAngleTheorem,
        state1WithPropagation,
        [A, B, C, D],
        [],
        [angleDAB, angleBCD]
    )

    if error:
        print(formatError(error))
        return

    finalState = propagateEqualAngles(result2)
    finalAngleDAB = next((x for x in finalState.angles if x.angle == angleDAB), None)
    if finalAngleDAB:
        value = finalAngleDAB.measure.evaluate()
        if value is not None:
            print(f"Final Result:")
            print(f"============")
            print(f"∠DAB = {value}° (Expected: 110°)")
            print(f"Verification: {'✓ Successful' if abs(value - 110) < 1e-10 else '✗ Failed'}")

def verify_q3():
    E = makePoint("E")
    A = makePoint("A")
    C = makePoint("C")
    B = makePoint("B")
    D = makePoint("D")

    angleABC = makeAngle(A, B, C)
    angleBCA = makeAngle(B, C, A)
    angleBCD = makeAngle(B, C, D)
    angleECD = makeAngle(E, C, D)
    angleBCE = makeAngle(B, C, E)
    angleDCB = makeAngle(D, C, B)
    angleECB = makeAngle(E, C, B)

    initial_facts = [
        GeometricFact(type_="Collinear", points=[E, C, A]),
        GeometricFact(type_="Parallel", lines=[makeLine(C, D), makeLine(A, B)])
    ]
    initial_angles = [
        AngleStatement(angleABC, 40.0),
        AngleStatement(angleBCA, 90.0),
        AngleStatement(angleBCE, 90.0)
    ]

    initialState = GeometricState(facts=initial_facts, angles=initial_angles)
    print("Initial State:")
    print("=============")
    for fact in initialState.facts:
        print(f"• {fact}")
    for angle in initialState.angles:
        print(f"• {angle}")
    print()

    result1, error = applyGeometricTheoremWithErrors(
        adjacentComplementaryAngleTheorem,
        initialState,
        [E, C, A],
        [],
        [angleBCA, angleBCE]
    )

    if error:
        print(formatError(error))
        return

    state1WithPropagation = propagateEqualAngles(result1)

    result2, error = applyGeometricTheoremWithErrors(
        parallelAlternateInteriorAnglesTheorem,
        state1WithPropagation,
        [],
        [makeLine(C, D), makeLine(A, B)],
        [angleABC, angleDCB]
    )

    if error:
        print(formatError(error))
        return

    state2WithPropagation = propagateEqualAngles(result2)

    result3, error = applyGeometricTheoremWithErrors(
        angleAdditionTheorem,
        state2WithPropagation,
        [],
        [],
        [angleECB, angleBCE, angleDCB]
    )

    if error:
        print(formatError(error))
        return

    finalState = propagateEqualAngles(result3)
    finalAngleECB = next((x for x in finalState.angles if x.angle == angleECB), None)
    if finalAngleECB:
        value = finalAngleECB.measure.evaluate()
        if value is not None:
            ecd_value = 180 - value
            print(f"Final Result:")
            print(f"============")
            print(f"∠ECD = {ecd_value}° (Expected: 50°)")
            print(f"Verification: {'✓ Successful' if abs(ecd_value - 50) < 1e-10 else '✗ Failed'}")




# verify_q1()
if __name__ == "__main__":
    pass

