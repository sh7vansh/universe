import sys
import os
import math

sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, ExtensionClass, mat_mul

def frobenius_norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

def bind_pure3(machine, A, B, name):
    M_AB = mat_mul(A.matrix, B.matrix)
    dim = 8
    # vector space dimension squared?
    energy = (dim**2) * math.log(frobenius_norm(M_AB))
    ext = ExtensionClass(name, energy)
    return machine.exact_sequence_reconstruction(A, B, ext)

machine = CategoricalMachine()
u_quarks = [machine.get_simple(3, color=f"c{i}") for i in range(12)]
d_quarks = [machine.get_simple(5, color=f"c{i}") for i in range(12)]

p1_temp = bind_pure3(machine, u_quarks[0], u_quarks[1], "Strong")
p1 = bind_pure3(machine, p1_temp, d_quarks[0], "Strong")

n1_temp = bind_pure3(machine, u_quarks[2], d_quarks[1], "Strong")
n1 = bind_pure3(machine, n1_temp, d_quarks[2], "Strong")

p2_temp = bind_pure3(machine, u_quarks[3], u_quarks[4], "Strong")
p2 = bind_pure3(machine, p2_temp, d_quarks[3], "Strong")

n2_temp = bind_pure3(machine, u_quarks[5], d_quarks[4], "Strong")
n2 = bind_pure3(machine, n2_temp, d_quarks[5], "Strong")

alpha_temp = bind_pure3(machine, p1, p2, "Strong")
alpha_temp2 = bind_pure3(machine, alpha_temp, n1, "Strong")
he_nuc = bind_pure3(machine, alpha_temp2, n2, "Strong")

print(f"Proton: {p1.mass:.2f}")
print(f"Neutron: {n1.mass:.2f}")
print(f"Helium Nuc: {he_nuc.mass:.2f}")
