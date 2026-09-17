import sys
import os
import math
import cmath

sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, mat_mul

machine = CategoricalMachine()
u = machine.get_simple(3)
d = machine.get_simple(5)
d_bar = machine.get_simple(5, is_anti=True)

M_u = u.matrix
M_d = d.matrix
M_d_bar = d_bar.matrix

def frobenius_norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

print("Norm M_u:", frobenius_norm(M_u))
print("Norm M_d:", frobenius_norm(M_d))
print("Norm M_d_bar:", frobenius_norm(M_d_bar))

M_u_d_bar = mat_mul(M_u, M_d_bar)
print("Norm M_u M_d_bar:", frobenius_norm(M_u_d_bar))

M_u_u = mat_mul(M_u, M_u)
print("Norm M_u M_u:", frobenius_norm(M_u_u))

M_u_d = mat_mul(M_u, M_d)
print("Norm M_u M_d:", frobenius_norm(M_u_d))
