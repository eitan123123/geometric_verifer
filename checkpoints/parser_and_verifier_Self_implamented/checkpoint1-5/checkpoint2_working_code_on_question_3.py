import os
from typing import List, Optional, Union


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
        # Hash based on the string 'name'
        return hash(self.name)

    def __repr__(self):
        return f"{self.name}"

    def __str__(self):
        return self.name


class Line:
    def __init__(self, start_point: Point, end_point: Point):
        self.startPoint = start_point
        self.endPoint = end_point

    def __eq__(self, other):
        if not isinstance(other, Line):
            return False
        return (
                (self.startPoint == other.startPoint and self.endPoint == other.endPoint)
                or (self.startPoint == other.endPoint and self.endPoint == other.startPoint)
        )

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


class Angle:
    """
    An angle is defined by three points:
    - point1 : first point defining the angle
    - vertex : the vertex point of the angle
    - point2 : second point defining the angle
    """

    def __init__(self, p1: Point, v: Point, p2: Point):
        self.point1 = p1
        self.vertex = v
        self.point2 = p2

    def __eq__(self, other):
        if not isinstance(other, Angle):
            return False
        return (
                self.point1 == other.point1
                and self.vertex == other.vertex
                and self.point2 == other.point2
        )

    def __repr__(self):
        return f"Angle({self.point1}, {self.vertex}, {self.point2})"

    def __str__(self):
        return f"Angle({self.point1}, {self.vertex}, {self.point2})"


class AngleStatement:
    """
    Associates an Angle with its measure in degrees (float).
    """

    def __init__(self, angle: Angle, measure: float):
        self.angle = angle
        self.measure = measure

    def __repr__(self):
        return f"Measure({self.angle}) = {self.measure}°"

    def __str__(self):
        return f"Measure({self.angle}) = {self.measure}°"


# -----------------------------
# Helper Constructor Functions
# -----------------------------

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
        self.points = points if points else []
        self.lines = lines if lines else []
        self.angles = angles if angles else []
        self.value = value
        self.relatedFacts = related_facts if related_facts else []

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
    """
    Holds the current known facts, lengths, and angles (with measures).
    """

    def __init__(
            self,
            facts: List[GeometricFact],
            lengths: List[LengthStatement] = None,
            angles: List[AngleStatement] = None
    ):
        self.facts = facts if facts else []
        self.lengths = lengths if lengths else []
        self.angles = angles if angles else []

    def __repr__(self):
        return f"GeometricState(facts={self.facts}, angles={self.angles})"


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
    """
    same_vertex = (angle1.vertex == angle2.vertex)

    # They share a point other than the vertex:
    share_one_ray = (
            (angle1.point1 == angle2.point1 or
             angle1.point1 == angle2.point2 or
             angle1.point2 == angle2.point1 or
             angle1.point2 == angle2.point2)
            and not (angle1.point1 == angle2.point1 and angle1.point2 == angle2.point2)
            and not (angle1.point1 == angle2.point2 and angle1.point2 == angle2.point1)
    )

    return same_vertex and share_one_ray


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
        TheoremRequirement(type_="collinear"),  # 3 points that form the line
        TheoremRequirement(type_="angle_measure")  # The angle we know
    ],
    conclusions=[
        TheoremConclusion(type_="angle_measure", related_facts=["complementary_angles"])
    ]
)

parallelAlternateInteriorAnglesTheorem = TheoremRule(
    name="parallel_property_alternate_interior_angle",
    requirements=[
        TheoremRequirement(type_="parallel")
    ],
    conclusions=[
        TheoremConclusion(type_="angle_equal", related_facts=["parallel_angles"])
    ]
)


# -----------------------------
# Filling Requirements/Conclusions
# -----------------------------

def fillRequirements(reqs: List[TheoremRequirement],
                     points: List[Point],
                     lines: List[Line],
                     angles: List[Angle]) -> List[TheoremRequirement]:
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
            # Ad-hoc approach from the original Lean code
            if len(angles) >= 3:
                # For demonstration, pick different angles for each "angle_measure".
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

        # "angle_sum" special logic
        if concl.type == "angle_sum":
            if len(angles) >= 3:
                new_concl.angles = [angles[0], angles[1], angles[2]]

        # "angle_measure" with "complementary_angles"
        if concl.type == "angle_measure" and "complementary_angles" in concl.relatedFacts:
            if len(angles) >= 2:
                new_concl.angles = [angles[1]]

        filled.append(new_concl)
    return filled


# -----------------------------
# Angle Propagation (Equality)
# -----------------------------

def propagateEqualAnglesHelper(state: GeometricState) -> Optional[GeometricState]:
    """
    Look for AngleEqual facts in state.facts. If one angle has a known measure,
    copy that measure to the other angle if not already known.
    """
    changed_something = False
    new_angles = list(state.angles)

    for fact in state.facts:
        if fact.type == "AngleEqual" and len(fact.angles) == 2:
            angle1, angle2 = fact.angles
            measure1 = next((x for x in new_angles if x.angle == angle1), None)
            measure2 = next((x for x in new_angles if x.angle == angle2), None)

            if measure1 and not measure2:
                new_angles.append(AngleStatement(angle=angle2, measure=measure1.measure))
                changed_something = True
            elif measure2 and not measure1:
                new_angles.append(AngleStatement(angle=angle1, measure=measure2.measure))
                changed_something = True

    if changed_something:
        return GeometricState(facts=state.facts, lengths=state.lengths, angles=new_angles)
    else:
        return None


def propagateEqualAngles(state: GeometricState, size: int = 10000) -> GeometricState:
    """
    Repeatedly propagate angle equalities until no more changes occur or we reach the iteration limit.
    """
    if size == 0:
        return state
    new_state = propagateEqualAnglesHelper(state)
    if new_state is not None:
        return propagateEqualAngles(new_state, size - 1)
    else:
        return state


# -----------------------------
# Apply Conclusions to State
# -----------------------------

def applyConclusion(state: GeometricState, concl: TheoremConclusion) -> GeometricState:
    """
    Modify the state based on the conclusion type.
    """
    new_facts = list(state.facts)
    new_angles = list(state.angles)

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
                # Overwrite or add new measure
                new_angles = [x for x in new_angles if x.angle != targetAngle]
                new_angles.append(AngleStatement(angle=targetAngle, measure=total))
                return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)

            # complementary_angles
            elif "complementary_angles" in concl.relatedFacts:
                known = None
                for x in new_angles:
                    if x.angle.vertex == targetAngle.vertex and x.angle != targetAngle:
                        known = x
                        break
                if not known:
                    return state
                comp_val = 180.0 - known.measure
                new_angles = [x for x in new_angles if x.angle != targetAngle]
                new_angles.append(AngleStatement(angle=targetAngle, measure=comp_val))
                return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)

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

            # equal_angle_transfer
            elif "equal_angle_transfer" in concl.relatedFacts:
                source_measure = None
                for x in new_angles:
                    if x.angle != targetAngle:
                        # Check if there's a matching AngleEqual fact
                        has_equality = any(
                            f for f in new_facts
                            if f.type == "AngleEqual" and
                            x.angle in f.angles and
                            targetAngle in f.angles
                        )
                        if has_equality:
                            source_measure = x
                            break
                if source_measure:
                    new_angles = [z for z in new_angles if z.angle != targetAngle]
                    new_angles.append(AngleStatement(angle=targetAngle, measure=source_measure.measure))
                return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)

            else:
                # direct measure assignment / copying existing measure
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
            new_fact = GeometricFact(type_="AngleEqual", angles=[a1, a2], related_facts=["angle_equal"])
            new_facts.append(new_fact)
            return GeometricState(facts=new_facts, lengths=state.lengths, angles=new_angles)
        return state

    # angle_sum
    elif concl.type == "angle_sum":
        if len(concl.angles) == 3:
            resultA, angle1, angle2 = concl.angles[0], concl.angles[1], concl.angles[2]
            m1 = next((x for x in new_angles if x.angle == angle1), None)
            m2 = next((x for x in new_angles if x.angle == angle2), None)
            if m1 and m2:
                # original code logic: angle_sum = difference of the two angles
                new_val = m1.measure - m2.measure
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
    if req.type == "collinear":
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
    """
    Attempt to apply the theorem to the state with the given points/lines/angles.
    Returns (new_state, debug_string).

    If any requirement fails, we short-circuit and include the reason in our return message.
    """
    filled_requirements = fillRequirements(rule.requirements, points, lines, angles)
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

def writeToFile(content: str) -> None:
    """
    Writes the given content to a text file. Change the path to whatever
    works for you.
    """
    path = os.path.join(
        os.path.expanduser("~"),
        "Desktop",
        "lean",
        "lean porjects",
        "another",
        "another",
        "perfect_output.txt"
    )
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)


# -----------------------------
# Main Function
# -----------------------------

def main():
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
        print(output)
        writeToFile(output + "\nProof Verification Complete\n")
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

    if result2 is None:
        output += "Failed to apply parallel angles theorem\n" + debug2
        print(output)
        writeToFile(output + "\nProof Verification Complete\n")
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
        writeToFile(output + "\nProof Verification Complete\n")
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
    writeToFile(output + "\nProof Verification Complete\n")


if __name__ == "__main__":
    main()
