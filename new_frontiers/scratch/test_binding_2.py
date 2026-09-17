import sys
import os
import cmath

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

machine = CategoricalMachine()

u1 = machine.get_simple(3, color="red")
d = machine.get_simple(5, color="green")

# Let's check u1 and d commutator using their exact implementation
def mat_mul(m1, m2):
    n = len(m1)
    m = len(m2[0])
    p = len(m2)
    result = [[complex(0, 0)] * m for _ in range(n)]
    for i in range(n):
        for j in range(m):
            for k in range(p):
                result[i][j] += m1[i][k] * m2[k][j]
    return result

def mat_sub(m1, m2):
    return [[m1[i][j] - m2[i][j] for j in range(len(m1[0]))] for i in range(len(m1))]

AB = mat_mul(u1.matrix, d.matrix)
BA = mat_mul(d.matrix, u1.matrix)
diff = mat_sub(AB, BA)
print("diff (u, d):", diff)

# And frobenius norm:
import math
def norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

print("norm:", norm(diff))
