import sys
import os
sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

machine = CategoricalMachine()

u1 = machine.get_simple(3, color="red")
u2 = machine.get_simple(3, color="blue")
d = machine.get_simple(5, color="green")

# Dummy extension just to compile the composite
dummy = ExtensionClass("Dummy", 0.0)

uu = machine.exact_sequence_reconstruction(u1, u2, dummy)

def calc_friction(objA, objB):
    M_A = objA.matrix
    M_B = objB.matrix
    AB = [[complex(0,0)]*2 for _ in range(2)]
    BA = [[complex(0,0)]*2 for _ in range(2)]
    for i in range(2):
        for j in range(2):
            for k in range(2):
                AB[i][j] += M_A[i][k] * M_B[k][j]
                BA[i][j] += M_B[i][k] * M_A[k][j]
    diff = [[AB[i][j] - BA[i][j] for j in range(2)] for i in range(2)]
    mag = sum(abs(c) for r in diff for c in r)
    return mag

print(f"Friction U(3) + U(3): {calc_friction(u1, u2)}")
print(f"Friction (UU) + D(5): {calc_friction(uu, d)}")

# Build Proton
proton = machine.exact_sequence_reconstruction(uu, d, dummy)

# Let's check Proton + Electron (Hydrogen)
e = machine.get_simple(2)
print(f"Friction Proton(45) + e(2): {calc_friction(proton, e)}")

