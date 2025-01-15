import os
from typing import List, Optional, Union
from typing import Union, Optional
from dataclasses import dataclass
import sympy as sp
from typing import List, Dict, Set, Optional, Union


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
                 measure: Union[float, str, SymbolicExpression]):
        self.angle = angle
        if isinstance(measure, (int, float)):
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
    """
    Represents a geometric fact in the system, which could be collinearity, parallel lines,
    angle equalities, etc.
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

        # Handle points based on fact type
        if points:
            if self.type == "Collinear":
                # For collinear points, any order is valid
                # Store in sorted order for consistency
                self.points = sorted(points, key=lambda p: p.name)
            elif self.type == "Triangle":
                # For triangles, all rotations and reversals are equal
                # Start with smallest point name and try both orientations
                min_idx = min(range(len(points)), key=lambda i: points[i].name)
                rotated = points[min_idx:] + points[:min_idx]
                reversed_rotated = [rotated[0]] + list(reversed(rotated[1:]))
                names_normal = [p.name for p in rotated]
                names_reversed = [p.name for p in reversed_rotated]
                self.points = reversed_rotated if names_reversed < names_normal else rotated
            elif self.type in ["Parallelogram", "Shape"]:
                # For quadrilaterals and higher, maintain cyclic order but start with smallest point
                min_idx = min(range(len(points)), key=lambda i: points[i].name)
                self.points = points[min_idx:] + points[:min_idx]
            else:
                self.points = points
        else:
            self.points = []

        # Handle lines (order doesn't matter for pairs)
        if lines and len(lines) == 2 and self.type in ["Parallel", "Perpendicular"]:
            # For parallel/perpendicular, order of line pairs doesn't matter
            self.lines = sorted(lines, key=lambda l: (l.startPoint.name, l.endPoint.name))
        else:
            self.lines = lines if lines else []

        # Handle angles
        if angles and self.type == "AngleEqual":
            # For angle equality, order doesn't matter
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

        elif self.type == "Triangle":
            # All rotations and reversals are equal
            pts1 = [p.name for p in self.points]
            pts2 = [p.name for p in other.points]
            all_rotations = [pts1[i:] + pts1[:i] for i in range(len(pts1))]
            all_rotations.extend([list(reversed(r)) for r in all_rotations])
            return pts2 in all_rotations

        elif self.type in ["Parallel", "Perpendicular"]:
            # Order of lines doesn't matter
            return set(self.lines) == set(other.lines)

        elif self.type == "AngleEqual":
            # Order of angles doesn't matter
            return set(self.angles) == set(other.angles)

        elif self.type in ["Parallelogram", "Shape"]:
            # Compare cyclic rotations starting from smallest point
            return self.points == other.points or list(reversed(self.points)) == other.points

        # For other types, compare directly
        return (self.points == other.points and
                self.lines == other.lines and
                self.angles == other.angles and
                self.value == other.value)

    def __hash__(self):
        if self.type == "Collinear":
            return hash((self.type, frozenset(p.name for p in self.points)))
        elif self.type == "Triangle":
            return hash((self.type, frozenset(p.name for p in self.points)))
        elif self.type in ["Parallel", "Perpendicular"]:
            return hash((self.type, frozenset((l.startPoint.name, l.endPoint.name) for l in self.lines)))
        elif self.type == "AngleEqual":
            return hash(
                (self.type, frozenset((a.vertex.name, frozenset([a.point1.name, a.point2.name])) for a in self.angles)))
        else:
            return hash((self.type,
                         tuple(p.name for p in self.points),
                         tuple((l.startPoint.name, l.endPoint.name) for l in self.lines),
                         tuple((a.vertex.name, frozenset([a.point1.name, a.point2.name])) for a in self.angles),
                         self.value))

    def __repr__(self):
        if self.type == "Collinear":
            pts = ",".join(str(p) for p in self.points)
            return f"Collinear({pts})"
        elif self.type == "LengthSum":
            lns = ",".join(str(l) for l in self.lines)
            return f"LengthSum({lns})"
        elif self.type == "Parallel":
            lns = ",".join(str(l) for l in self.lines)
            return f"Parallel({lns})"
        elif self.type == "Perpendicular":
            lns = ",".join(str(l) for l in self.lines)
            return f"Perpendicular({lns})"
        elif self.type == "AngleEqual":
            angs = ",".join(str(a) for a in self.angles)
            return f"AngleEqual({angs})"
        elif self.type == "Parallelogram":
            pts = ",".join(str(p) for p in self.points)
            return f"Parallelogram({pts})"
        elif self.type == "AngleSum":
            angs = ",".join(str(a) for a in self.angles)
            return f"AngleSum({angs}) = {self.value}"
        else:
            return f"Fact({self.type})"


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

def propagateEqualAngles(state: GeometricState, size: int = 10000) -> GeometricState:
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
                if len(relevant) == 0:
                    return state
                total = sum(x.measure for x in relevant)
                new_angles = [x for x in new_angles if x.angle != targetAngle]
                new_angles.append(AngleStatement(angle=targetAngle, measure=total))
                return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)

            # complementary_angles
            elif "complementary_angles" in concl.relatedFacts:
                if len(concl.angles) == 1:
                    targetAngle = concl.angles[0]
                    known = next((x for x in new_angles if x.angle != targetAngle
                                  and x.angle.vertex == targetAngle.vertex), None)
                    if known:
                        comp_val = SymbolicExpression(sp.Number(180.0) - known.measure.expr)
                        new_angles = [x for x in new_angles if x.angle != targetAngle]
                        new_angles.append(AngleStatement(angle=targetAngle, measure=comp_val))
                        return GeometricState(facts=new_facts, lengths=state.lengths,
                                              angles=new_angles)

            # For parallel angles theorem
            elif "parallel_angles" in concl.relatedFacts:
                targetAngle = concl.angles[0]
                # Find a measure from any equal angle
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
                if len(relevant) == 0:
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
                existing = next((x for x in new_angles if x.angle == targetAngle), None)
                if not existing:
                    return state
                new_angles = [x for x in new_angles if x.angle != targetAngle]
                new_angles.append(AngleStatement(angle=targetAngle, measure=existing.measure))
                return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)
        return state

    # angle_equal
    elif concl.type == "angle_equal":
        if len(concl.angles) == 2:
            a1, a2 = concl.angles
            # Add the equality fact
            new_fact = GeometricFact(type_="AngleEqual", angles=[a1, a2],
                                     related_facts=["angle_equal"])
            new_facts.append(new_fact)

            # Propagate the measure if one angle has it
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
                # Use the sympy expressions for addition
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

def checkRequirementWithDebug(state: GeometricState, req: TheoremRequirement) -> (bool, str):
    """
    Checks if a given requirement is met and returns (met?, debug_message).
    """
    if req.type == "shape":
        needed_points = set(req.points)
        found_fact = None
        for fact in state.facts:
            if fact.type == "Shape":
                fact_points = set(fact.points)
                if fact_points == needed_points:
                    found_fact = fact
                    break
        if found_fact:
            debug_msg = (f"Checking shape requirement for points: {req.points}\n"
                         f"Found shape fact: {found_fact}")
            return True, debug_msg
        else:
            shape_facts = [f for f in state.facts if f.type == "Shape"]
            shape_list = "\n".join([f"  • {f.points}" for f in shape_facts])
            debug_msg = (
                f"Checking shape requirement for points: {req.points}\n"
                f"Could not verify shape:\n"
                f"- Looking for shape with points {req.points}\n"
                f"- Existing shape facts in our state:\n"
                f"{shape_list}\n"
                f"- These points are not part of any known shape relationship\n"
            )
            return False, debug_msg

    elif req.type == "collinear":
        needed = set(req.points)
        found_fact = None
        for fact in state.facts:
            if fact.type == "Collinear":
                fact_points = set(fact.points)
                if needed.issubset(fact_points):
                    found_fact = fact
                    break
        if found_fact:
            debug_msg = (f"Checking collinear requirement for points: {req.points}\n"
                         f"Found collinear fact: {found_fact}")
            return True, debug_msg
        else:
            collinear_facts = [f for f in state.facts if f.type == "Collinear"]
            collinear_list = "\n".join([f"  • {f.points}" for f in collinear_facts])
            debug_msg = (
                f"Checking collinear requirement for points: {req.points}\n"
                f"Could not verify collinearity:\n"
                f"- Looking for points {req.points} to be collinear\n"
                f"- Existing collinear facts in our state:\n"
                f"{collinear_list}\n"
                f"- These points are not part of any known collinear relationship\n"
            )
            return False, debug_msg






    elif req.type == "angle_measure":
        if len(req.angles) == 1:
            angle = req.angles[0]
            measure = next((x for x in state.angles if x.angle == angle), None)
            debug_msg = (
                f"Checking single angle measure for {angle}\n"
                f"Found measurement: {measure}"
            )
            return (measure is not None), debug_msg
        elif len(req.angles) >= 2:
            angle1 = req.angles[0]
            angle2 = req.angles[1]
            measure1 = next((x for x in state.angles if x.angle == angle1), None)
            measure2 = next((x for x in state.angles if x.angle == angle2), None)
            debug_msg = (
                f"Checking measures for angles:\n"
                f"  {angle1}: {measure1}\n"
                f"  {angle2}: {measure2}\n"
            )
            return (measure1 is not None and measure2 is not None), debug_msg
        else:
            return False, "No angles provided for angle measure check"

    elif req.type == "parallelogram":
        needed_points = set(req.points)
        found_fact = None
        for fact in state.facts:
            if fact.type == "Parallelogram":
                fact_points = set(fact.points)
                if needed_points == fact_points:
                    found_fact = fact
                    break
        if found_fact:
            debug_msg = (f"Checking parallelogram requirement for points: {req.points}\n"
                         f"Found parallelogram fact: {found_fact}")
            return True, debug_msg
        else:
            parallelogram_facts = [f for f in state.facts if f.type == "Parallelogram"]
            parallelogram_list = "\n".join([f"  • {f.points}" for f in parallelogram_facts])
            debug_msg = (
                f"Checking parallelogram requirement for points: {req.points}\n"
                f"Could not verify parallelogram:\n"
                f"- Looking for parallelogram with points {req.points}\n"
                f"- Existing parallelogram facts in our state:\n"
                f"{parallelogram_list}\n"
                f"- These points are not part of any known parallelogram relationship\n"
            )
            return False, debug_msg


    elif req.type == "parallel":
        needed = req.lines
        found_fact = None
        for fact in state.facts:
            if fact.type == "Parallel":
                if fact.lines == needed or fact.lines[::-1] == needed:
                    found_fact = fact
                    break
        debug_msg = (
            f"Checking parallel requirement for lines: {needed}\n"
            f"Found parallel fact: {found_fact}"
        )
        return (found_fact is not None), debug_msg

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
            is_adj = same_vertex and share_ray
            debug_msg = (
                f"Checking adjacency between angles:\n"
                f"  Angle 1: {angle1}\n"
                f"  Angle 2: {angle2}\n"
                f"  Share vertex: {same_vertex}\n"
                f"  Share ray: {share_ray}\n"
                f"  Adjacent: {is_adj}\n"
            )
            return is_adj, debug_msg
        else:
            return False, "Invalid number of angles for adjacency check"

    else:
        return False, f"Unrecognized requirement type: {req.type}"


# -----------------------------
# Main Theorem Application
# -----------------------------

def applyGeometricTheoremWithDebug(
        rule: TheoremRule,
        state: GeometricState,
        points: List[Point],
        lines: List[Line],
        angles: List[Angle]
) -> (Optional[GeometricState], str):
    filled_requirements = fillRequirements(rule.requirements, points, lines, angles, state)  # Add state here
    filled_conclusions = fillConclusions(rule.conclusions, points, lines, angles)

    # Build debug info for requirements/conclusions
    requirements_debug = "\nDEBUG - Filled Requirements Structure:\n"
    for req in filled_requirements:
        requirements_debug += (
            f"Requirement:\n"
            f"  Type: {req.type}\n"
            f"  Points: {req.points}\n"
            f"  Lines: {req.lines}\n"
            f"  Angles: {req.angles}\n"
            f"  Value: {req.value}\n"
        )

    conclusions_debug = "\nDEBUG - Filled Conclusions Structure:\n"
    for c in filled_conclusions:
        conclusions_debug += (
            f"Conclusion:\n"
            f"  Type: {c.type}\n"
            f"  Points: {c.points}\n"
            f"  Lines: {c.lines}\n"
            f"  Angles: {c.angles}\n"
            f"  Value: {c.value}\n"
            f"  Related Facts: {c.relatedFacts}\n"
        )

    initial_debug = (
        f"Applying theorem: {rule.name}\n"
        f"{requirements_debug}"
        f"{conclusions_debug}"
        "Current State:\n"
        "Angles in state:\n"
    )
    for ang_st in state.angles:
        initial_debug += f"  • {ang_st}\n"

    initial_debug += "\nFilled Requirements:\n"
    for req in filled_requirements:
        initial_debug += f"  • Type: {req.type}\n"
        if req.angles:
            initial_debug += "    Angles:\n"
            for a in req.angles:
                initial_debug += f"      - {a}\n"
        if req.lines:
            initial_debug += "    Lines:\n"
            for l in req.lines:
                initial_debug += f"      - {l}\n"

    initial_debug += "\nFilled Conclusions:\n"
    for c in filled_conclusions:
        initial_debug += f"  • Type: {c.type}\n"
        if c.angles:
            initial_debug += "    Angles:\n"
            for a in c.angles:
                initial_debug += f"      - {a}\n"
        initial_debug += f"    Related Facts: {c.relatedFacts}\n"

    initial_debug += "\nChecking requirements:\n"

    # We'll accumulate all debug text here
    full_debug = initial_debug

    # ---- SHORT-CIRCUIT LOGIC ----
    # Check each requirement in order. If one fails, STOP and return a message.
    for req in filled_requirements:
        met, debug_str = checkRequirementWithDebug(state, req)

        # Add the debug info from checkRequirementWithDebug
        full_debug += (
            f"Requirement {req.type}:\n"
            f"{debug_str}\n"
            f"Met: {met}\n\n"
        )

        if not met:
            # SHORT-CIRCUIT: We immediately stop and return the reason
            failure_msg = (
                    full_debug
                    + f"Requirement '{req.type}' was NOT met.\n"
                    + "The reason:\n"
                    + debug_str  # This includes the explanation of *why* it failed
                    + "\nStopping theorem application immediately.\n"
            )
            return None, failure_msg

    # If we get here, *all* requirements are met
    resultState = applyConclusions(state, filled_conclusions)

    # Build the final success debug
    final_debug = (
            full_debug
            + "\nApplying conclusions...\nFinal state:\nAngles in final state:\n"
    )
    for a in resultState.angles:
        final_debug += f"  • {a}\n"

    return resultState, final_debug


# -----------------------------
# File writing
# -----------------------------




# -----------------------------
# Main Function
# -----------------------------





def verify_q1():
    # Create points & angles as before
    X = makePoint("X")
    W = makePoint("W")
    Z = makePoint("Z")
    Y = makePoint("Y")

    angleWZY = makeAngle(W, Z, Y)
    angleXWZ = makeAngle(X, W, Z)
    angleYXW = makeAngle(Y, X, W)
    angleZYX = makeAngle(Z, Y, X)

    # Initial angle measurements with variables
    angleWZY_measure = AngleStatement(angleWZY, "a + 2")
    angleXWZ_measure = AngleStatement(angleXWZ, "a/2 + 8")
    angleYXW_measure = AngleStatement(angleYXW, "a")
    angleZYX_measure = AngleStatement(angleZYX, "a - 28")

    # Initial state
    initial_facts = [
        GeometricFact(type_="Shape", points=[X, W, Z, Y])
    ]
    initial_angles = [
        angleWZY_measure,
        angleXWZ_measure,
        angleYXW_measure,
        angleZYX_measure
    ]

    initialState = GeometricState(facts=initial_facts, angles=initial_angles)

    # Debug output
    output = "Quadrilateral Angle Problem Verification\n"
    output += "===================================\n\n"
    output += "Initial State:\n"
    for ang in initialState.angles:
        output += f"• {ang}\n"

    # Step 1: Apply quadrilateral angle sum theorem
    result1, debug1 = applyGeometricTheoremWithDebug(
        quadrilateralAngleSumTheorem,
        initialState,
        [X, W, Z, Y],
        [],
        [angleWZY, angleXWZ, angleYXW, angleZYX]
    )

    if result1 is None:
        output += "Failed to apply quadrilateral angle sum theorem\n" + debug1
        print(output)
        return

    state1 = result1
    output += "\nStep 1: Applied Quadrilateral Angle Sum\n" + debug1

    # Propagate and solve equations
    state1WithPropagation = propagateEqualAngles(state1)
    output += "\nAfter First Propagation:\n"
    for ang in state1WithPropagation.angles:
        output += f"• {ang}\n"

    # Final check
    finalAngleZYX = next(
        (x for x in state1WithPropagation.angles if x.angle == angleZYX),
        None
    )

    if finalAngleZYX:
        value = finalAngleZYX.measure.evaluate()
        if value is not None:
            output += f"\nFinal ∠ZYX = {value}°\n"
            output += f"Verification: {'Success' if abs(value - 80) < 1e-10 else 'Failed'}\n"

    print(output)

def verify_q2():
    # 1. CREATE POINTS
    pointA = makePoint("A")
    pointB = makePoint("B")
    pointC = makePoint("C")
    pointD = makePoint("D")
    pointE = makePoint("E")

    # 2. CREATE LINES
    lineBA = makeLine(pointB, pointA)
    lineBC = makeLine(pointB, pointC)
    lineCD = makeLine(pointC, pointD)
    lineDA = makeLine(pointD, pointA)
    lineBE = makeLine(pointB, pointE)
    lineCE = makeLine(pointC, pointE)

    # 3. CREATE ANGLES - Critical angle order!
    angleBCD = makeAngle(pointB, pointC, pointD)  # This is the one we need to find first
    angleDCE = makeAngle(pointD, pointC, pointE)  # This is the known 70° angle
    angleDAB = makeAngle(pointD, pointA, pointB)  # The final angle we want

    # 4. INITIAL ANGLE MEASUREMENTS
    angleDCE_measure = AngleStatement(angleDCE, 70.0)

    # 5. INITIAL STATE
    initial_facts = [
        GeometricFact(type_="Collinear", points=[pointB, pointC, pointE]),
        GeometricFact(type_="Parallelogram", points=[pointA, pointB, pointC, pointD]),
        GeometricFact(type_="Shape", points=[pointD, pointC, pointE])
    ]
    initial_angles = [angleDCE_measure]

    initialState = GeometricState(facts=initial_facts, angles=initial_angles)

    # Build up an initial output string
    output = (
        "Geometric Proof Verification - Parallelogram Problem\n"
        "=============================================\n\n"
        "Initial State Details:\n"
        "---------------------\n"
    )
    for f in initialState.facts:
        output += f"• {f}\n"
    output += "\nInitial Angle Measurements:\n"
    for a in initialState.angles:
        output += f"• {a}\n"
    output += "\n"

    # ------------------
    # STEP 1: Adjacent Complementary Angles
    # ------------------
    result1, debug1 = applyGeometricTheoremWithDebug(
        adjacentComplementaryAngleTheorem,
        initialState,
        [pointB, pointC, pointE],
        [],
        [angleBCD, angleDCE]  # Order matters here - first the angle we want to find, then the known angle
    )

    if result1 is None:
        output += "Failed to apply complementary angles theorem:\n" + debug1
        print(output)
        return
    else:
        state1 = result1
        output += (
            "Step 1: Adjacent Complementary Angles Theorem\n"
            "----------------------------------------\n"
            + debug1 + "\n"
        )

    # Propagate angles after step 1
    state1WithPropagation = propagateEqualAngles(state1)
    output += (
        "\nState After First Propagation:\n"
        "----------------------------\n"
        "Angles after propagation:\n"
    )
    for ang_st in state1WithPropagation.angles:
        output += f"  • {ang_st}\n"
    output += "\n"

    # ------------------
    # STEP 2: Parallelogram Opposite Angles
    # ------------------
    result2, debug2 = applyGeometricTheoremWithDebug(
        parallelogramOppositeAngleTheorem,
        state1WithPropagation,
        [pointA, pointB, pointC, pointD],
        [],
        [angleDAB, angleBCD]
    )

    if result2 is None:
        output += "Failed to apply parallelogram opposite angles theorem\n" + debug2
        print(output + "\nProof Verification Complete\n")
        return
    else:
        state2 = result2
        output += (
            "Step 2: Parallelogram Opposite Angles Theorem\n"
            "----------------------------------------\n"
            + debug2 + "\n"
        )

    # Final propagation
    finalState = propagateEqualAngles(state2)
    output += (
        "\nFinal State:\n"
        "------------\n"
        "Angles after final propagation:\n"
    )
    for ang_st in finalState.angles:
        output += f"  • {ang_st}\n"
    output += "\n"

    # Check final angle
    finalAngleDAB = next((x for x in finalState.angles if x.angle == angleDAB), None)
    if finalAngleDAB:
        value = finalAngleDAB.measure.evaluate()
        if value is not None:
            output += (
                f"Final ∠DAB measure: {value}°\n"
                f"Verification {'successful' if abs(value - 110) < 1e-10 else 'failed'}\n"
            )
    else:
        output += "Failed to find final ∠DAB measurement\n"

    print(output + "\nProof Verification Complete\n")



def verify_q3():
    # 1. CREATE POINTS
    pointE = makePoint("E")
    pointA = makePoint("A")
    pointC = makePoint("C")
    pointB = makePoint("B")
    pointD = makePoint("D")

    # 2. CREATE LINES
    lineEA = makeLine(pointE, pointA)
    lineEC = makeLine(pointE, pointC)
    lineCA = makeLine(pointC, pointA)
    lineAB = makeLine(pointA, pointB)
    lineBC = makeLine(pointB, pointC)
    lineCD = makeLine(pointC, pointD)

    # 3. CREATE ANGLES
    angleABC = makeAngle(pointA, pointB, pointC)  # Angle at B between A and C
    angleBCA = makeAngle(pointB, pointC, pointA)  # Right angle at C
    angleBCD = makeAngle(pointB, pointC, pointD)  # Full angle at C
    angleECD = makeAngle(pointE, pointC, pointD)  # The angle we want to find
    angleBCE = makeAngle(pointB, pointC, pointE)  # 90-degree angle at C
    angleDCB = makeAngle(pointD, pointC, pointB)  # Alternate interior angle

    # 4. INITIAL ANGLE MEASUREMENTS
    angleABC_measure = AngleStatement(angleABC, 40.0)
    angleBCA_measure = AngleStatement(angleBCA, 90.0)
    angleBCE_measure = AngleStatement(angleBCE, 90.0)

    # 5. INITIAL STATE
    initial_facts = [
        GeometricFact(type_="Collinear", points=[pointE, pointC, pointA]),
        GeometricFact(type_="Parallel", lines=[lineCD, lineAB]),
        GeometricFact(type_="Shape", points=[pointC, pointA, pointB]),
        GeometricFact(type_="Shape", points=[pointE, pointC, pointD]),
        GeometricFact(type_="Shape", points=[pointD, pointC, pointB]),
        GeometricFact(type_="Shape", points=[pointE, pointC, pointB])
    ]
    initial_angles = [
        angleABC_measure,  # index 0
        angleBCA_measure,  # index 1
        angleBCE_measure  # index 2
    ]

    initialState = GeometricState(facts=initial_facts, angles=initial_angles)

    # Build up an initial output string
    output = (
        "Geometric Proof Verification\n"
        "========================\n\n"
        "Initial State Details:\n"
        "---------------------\n"
    )
    for f in initialState.facts:
        output += f"• {f}\n"
    output += "\nInitial Angle Measurements:\n"
    for a in initialState.angles:
        output += f"• {a}\n"
    output += "\n"

    # ------------------
    # STEP 1
    # ------------------
    result1, debug1 = applyGeometricTheoremWithDebug(
        adjacentComplementaryAngleTheorem,
        initialState,
        [pointE, pointC, pointA],
        [],
        [angleBCA, angleBCE]
    )

    if result1 is None:
        # If step 1 failed, print & write out the debug info and then stop the entire code
        output += "Failed to apply complementary angles theorem:\n" + debug1
        print(output + "\nProof Verification Complete\n")
        return
    else:
        state1 = result1
        output += (
                "Step 1: Adjacent Complementary Angles Theorem\n"
                "----------------------------------------\n"
                + debug1 + "\n"
        )

    # Propagate angles
    state1WithPropagation = propagateEqualAngles(state1)
    output += (
        "\nState After First Propagation:\n"
        "----------------------------\n"
        "Angles after propagation:\n"
    )
    for ang_st in state1WithPropagation.angles:
        output += f"  • {ang_st}\n"
    output += "\n"

    # ------------------
    # STEP 2
    # ------------------
    result2, debug2 = applyGeometricTheoremWithDebug(
        parallelAlternateInteriorAnglesTheorem,
        state1WithPropagation,
        [],
        [lineCD, lineAB],
        [angleABC, angleDCB]
    )
    print("\nAfter parallel theorem:")
    print("Facts:")
    for f in result2.facts:
        if f.type == "AngleEqual":
            print(f"  • {f}")
    print("Angles:")
    for a in result2.angles:
        print(f"  • {a}")

    if result2 is None:
        output += "Failed to apply parallel angles theorem\n" + debug2
        print(output + "\nProof Verification Complete\n")
        return
    else:
        state2 = result2
        output += (
                "Step 2: Parallel Alternate Interior Angles Theorem\n"
                "-------------------------------------------\n"
                + debug2 + "\n"
        )

    # Propagate angles again
    state2WithPropagation = propagateEqualAngles(state2)
    output += (
        "\nState After Second Propagation:\n"
        "-----------------------------\n"
        "Angles after propagation:\n"
    )
    for ang_st in state2WithPropagation.angles:
        output += f"  • {ang_st}\n"
    output += "\n"

    # Before angle addition
    output += (
        "\nState Before Angle Addition:\n"
        "-------------------------\n"
        "Checking angles BCE and DCB for adjacency:\n"
        f"BCE: vertex={angleBCE.vertex.name}, points={angleBCE.point1.name},{angleBCE.point2.name}\n"
        f"DCB: vertex={angleDCB.vertex.name}, points={angleDCB.point1.name},{angleDCB.point2.name}\n"
        f"Are adjacent: {areAdjacent(angleBCE, angleDCB)}\n\n"
    )

    # ------------------
    # STEP 3
    # ------------------
    result3, debug3 = applyGeometricTheoremWithDebug(
        angleAdditionTheorem,
        state2WithPropagation,
        [],
        [],
        [angleECD, angleBCE, angleDCB]
    )

    if result3 is None:
        output += (
                "Step 3: Angle Addition Theorem\n"
                "-------------------------\n"
                + debug3 + "\n"
                           "Failed to apply angle addition theorem\n"
        )
        print(output)
        return
    else:
        state3 = result3
        output += (
                "Step 3: Angle Addition Theorem\n"
                "-------------------------\n"
                + debug3 + "\n"
        )

    # Final propagation
    finalState = propagateEqualAngles(state3)
    output += (
        "\nState After Third Propagation:\n"
        "----------------------------\n"
        "Angles after propagation:\n"
    )
    for a_st in finalState.angles:
        output += f"  • {a_st}\n"
    output += "\n"

    finalAngleECD = next((x for x in finalState.angles if x.angle == angleECD), None)
    if finalAngleECD:
        output += (
            "Angle Addition Successful\n"
            f"Final ECD angle measure: {finalAngleECD.measure}°\n"
            "\nFinal State Summary:\n"
            "-------------------\n"
            "All angles in final state:\n"
        )
        for a_st in finalState.angles:
            output += f"  • {a_st}\n"
    else:
        output += "Failed to find final ECD angle measurement\n"

    # Print everything to console so you see the verification process
    print(output)

    # Write final output to file



# verify_q1()



# Create points
# Create points
A = makePoint("A")
B = makePoint("B")
C = makePoint("C")
F = makePoint("F")
L = makePoint("L")
D = makePoint("D")

# Create angles
angle_ABC = makeAngle(A, B, C)
angle_CBA = makeAngle(C, B, A)  # Same as ABC
angle_FLD = makeAngle(F, L, D)

# Create initial statements
abc_measure = AngleStatement(angle_ABC, "x")
fld_measure = AngleStatement(angle_FLD, "2*x-5")

# Create initial state with fact saying ABC equals FLD
initial_facts = [
    GeometricFact(type_="AngleEqual", angles=[angle_ABC, angle_FLD])
]
initial_angles = [abc_measure, fld_measure]

initialState = GeometricState(facts=initial_facts, angles=initial_angles)

print("Initial state (before any propagation):")
print("Equations in system:", initialState.equations.equations)
for ang in initialState.angles:
    print(f"{ang}")

# Now propagate
finalState = propagateEqualAngles(initialState)

print("\nAfter propagation:")
print("Equations in system:", finalState.equations.equations)
for ang in finalState.angles:
    print(f"{ang}")
    if ang.measure.evaluate() is not None:
        print(f"  Evaluated to: {ang.measure.evaluate()}")

# Try to find measure of CBA
cba_measure = next((x for x in finalState.angles if x.angle == angle_CBA), None)
if cba_measure:
    print(f"\nCBA measure: {cba_measure}")
    print(f"CBA evaluation: {cba_measure.measure.evaluate()}")