import sys
import os
import math

sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, mat_mul, mat_sub

machine = CategoricalMachine()
u1 = machine.get_simple(3)
u2 = machine.get_simple(3)
d = machine.get_simple(5)

M_u = u1.matrix
M_d = d.matrix

AB = mat_mul(M_u, M_d)
BA = mat_mul(M_d, M_u)
diff = mat_sub(AB, BA)

def frobenius_norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

print("Norm [M_u, M_d]:", frobenius_norm(diff))

