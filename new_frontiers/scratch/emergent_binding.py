import sys
import os
sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine

machine = CategoricalMachine()

u = machine.get_simple(3)
d = machine.get_simple(5)
e = machine.get_simple(2)

def calc_commutator_magnitude(objA, objB):
    M_A = objA.matrix
    M_B = objB.matrix
    
    # mat mul AB
    AB = [[complex(0,0)]*2 for _ in range(2)]
    for i in range(2):
        for j in range(2):
            for k in range(2):
                AB[i][j] += M_A[i][k] * M_B[k][j]
                
    # mat mul BA
    BA = [[complex(0,0)]*2 for _ in range(2)]
    for i in range(2):
        for j in range(2):
            for k in range(2):
                BA[i][j] += M_B[i][k] * M_A[k][j]
                
    # diff
    diff = [[AB[i][j] - BA[i][j] for j in range(2)] for i in range(2)]
    
    # sum of magnitudes
    mag = 0
    for r in diff:
        for c in r:
            mag += abs(c)
    return mag

print("--- EMERGENT BINDING METRICS (Commutator Magnitudes) ---")
print(f"Up (3) binding with Down (5): {calc_commutator_magnitude(u, d)}")
print(f"Up (3) binding with Electron (2): {calc_commutator_magnitude(u, e)}")
print(f"Electron (2) binding with Down (5): {calc_commutator_magnitude(e, d)}")
print(f"Up (3) binding with Up (3): {calc_commutator_magnitude(u, u)}")

