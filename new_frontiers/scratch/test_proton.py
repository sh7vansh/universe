import sys
import os
import cmath
import math

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

machine = CategoricalMachine()

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

def frobenius_norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

u1 = machine.get_simple(3, color="red")
u2 = machine.get_simple(3, color="blue")
d = machine.get_simple(5, color="green")

# Order 1: (u + d) + u
print("--- Order 1: (u + d) + u ---")
ud = machine.exact_sequence_reconstruction(u1, d)
diff1 = mat_sub(mat_mul(u1.matrix, d.matrix), mat_mul(d.matrix, u1.matrix))
norm1 = frobenius_norm(diff1)
print(f"Norm(u, d) = {norm1}")

proton1 = machine.exact_sequence_reconstruction(ud, u2)
diff2 = mat_sub(mat_mul(ud.matrix, u2.matrix), mat_mul(u2.matrix, ud.matrix))
norm2 = frobenius_norm(diff2)
print(f"Norm(ud, u) = {norm2}")
print(f"Total binding energy norm = {norm1 + norm2}")

# Order 2: (u + u) + d
print("\n--- Order 2: (u + u) + d ---")
uu = machine.exact_sequence_reconstruction(u1, u2)
diff3 = mat_sub(mat_mul(u1.matrix, u2.matrix), mat_mul(u2.matrix, u1.matrix))
norm3 = frobenius_norm(diff3)
print(f"Norm(u, u) = {norm3}")

proton2 = machine.exact_sequence_reconstruction(uu, d)
diff4 = mat_sub(mat_mul(uu.matrix, d.matrix), mat_mul(d.matrix, uu.matrix))
norm4 = frobenius_norm(diff4)
print(f"Norm(uu, d) = {norm4}")
print(f"Total binding energy norm = {norm3 + norm4}")

# Wait, what if we calculate the vector space dimension or trace?
