import sympy as sp
from z3 import *

# Step 1: Use SymPy to find possible values for x
x = sp.Symbol('x')
solutions_x = sp.solve(sp.Eq(sp.sin(x), 1/2), x)  # Find solutions in radians

# Convert to numerical values for Z3 (degrees for simplicity)
numeric_solutions_x = [float(sol.evalf()) for sol in solutions_x]

# Step 2: Use Z3 for logical constraint solving
x_z3 = Real('x')
y_z3 = Real('y')
s = Solver()

# Add found solutions as constraints in Z3
s.add(Or([x_z3 == sol for sol in numeric_solutions_x]))

# Add additional logical constraints
s.add(x_z3 + y_z3 == 180)  # Example: x + y = 180
s.add(y_z3 > 90)  # Example constraint

# Solve and output results
if s.check() == sat:
    print(s.model())  # Valid x and y assignments
else:
    print("No solution found")
