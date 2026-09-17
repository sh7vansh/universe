import sys
import os
import math

sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, ExtensionClass, mat_mul

def frobenius_norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

def calculate_loewy_friction(objA, objB):
    optimal_length = len(objA.factors) + len(objB.factors)
    accumulated_virtual_nodes = sum(len(ext.virtual_nodes) for ext in objA.extensions + objB.extensions)
    new_virtual_nodes = len(objA.factors) + len(objB.factors)
    total_loewy_length = optimal_length + accumulated_virtual_nodes + new_virtual_nodes
    friction = total_loewy_length - optimal_length
    return friction

machine = CategoricalMachine()

# 1. Derive the mathematical Pion Invariant (k)
u_quarks = [machine.get_simple(3, color=f"c{i}") for i in range(12)]
d_quarks = [machine.get_simple(5, color=f"c{i}") for i in range(12)]
electrons = [machine.get_simple(2, color=f"e{i}") for i in range(2)]

# Pion is the base unit of the strong force (u + anti-d)
anti_d = machine.get_simple(5, is_anti=True)
M_pion = mat_mul(u_quarks[0].matrix, anti_d.matrix)
pion_invariant_k = frobenius_norm(M_pion)

print(f"Emergent Pion Invariant (kappa): {pion_invariant_k:.4f}")

def bind_pion_invariant(machine, A, B, name):
    f = calculate_loewy_friction(A, B)
    energy = f * pion_invariant_k
    ext = ExtensionClass(name, energy)
    return machine.exact_sequence_reconstruction(A, B, ext)

# 2. Nucleosynthesis
p1_temp = bind_pion_invariant(machine, u_quarks[0], u_quarks[1], "Strong")
p1 = bind_pion_invariant(machine, p1_temp, d_quarks[0], "Strong")

p2_temp = bind_pion_invariant(machine, u_quarks[2], u_quarks[3], "Strong")
p2 = bind_pion_invariant(machine, p2_temp, d_quarks[1], "Strong")

n1_temp = bind_pion_invariant(machine, u_quarks[4], d_quarks[2], "Strong")
n1 = bind_pion_invariant(machine, n1_temp, d_quarks[3], "Strong")

n2_temp = bind_pion_invariant(machine, u_quarks[5], d_quarks[4], "Strong")
n2 = bind_pion_invariant(machine, n2_temp, d_quarks[5], "Strong")

alpha_temp = bind_pion_invariant(machine, p1, p2, "Strong")
alpha_temp2 = bind_pion_invariant(machine, alpha_temp, n1, "Strong")
he_nuc = bind_pion_invariant(machine, alpha_temp2, n2, "Strong")

print(f"Proton Mass: {p1.mass:.2f} MeV")
print(f"Neutron Mass: {n1.mass:.2f} MeV")
print(f"Helium Nucleus Mass: {he_nuc.mass:.2f} MeV")
