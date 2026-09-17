import sys
import os
import cmath

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

machine = CategoricalMachine()

u1 = machine.get_simple(3, color="red")
u2 = machine.get_simple(3, color="blue")
d = machine.get_simple(5, color="green")

# Let's look at the matrices M_u1, M_u2, M_d
print("u1 matrix:", u1.matrix)
print("u2 matrix:", u2.matrix)
print("d matrix:", d.matrix)

# Try calculating the commutator between u1 and u2
def mat_mul(m1, m2):
    return [[sum(a * b for a, b in zip(r, c)) for c in zip(*m2)] for r in m1]

def mat_sub(m1, m2):
    return [[a - b for a, b in zip(r1, r2)] for r1, r2 in zip(m1, m2)]

AB = mat_mul(u1.matrix, u2.matrix)
BA = mat_mul(u2.matrix, u1.matrix)
diff = mat_sub(AB, BA)
print("diff (u, u):", diff)

# What if we calculate diff (uu, d)
# Binding u1 and u2:
# In unified_categorical_engine, exact_sequence_reconstruction sets matrix_C = mat_mul(A.matrix, B.matrix)
# if ext has no matrix, it just multiplies M_A and M_B.
u_u = machine.exact_sequence_reconstruction(u1, u2)
print("u_u matrix:", u_u.matrix)

AB2 = mat_mul(u_u.matrix, d.matrix)
BA2 = mat_mul(d.matrix, u_u.matrix)
diff2 = mat_sub(AB2, BA2)
print("diff (uu, d):", diff2)

# What is the norm of diff2?
import math
def frobenius_norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

print("norm diff(u, u):", frobenius_norm(diff))
print("norm diff(uu, d):", frobenius_norm(diff2))
