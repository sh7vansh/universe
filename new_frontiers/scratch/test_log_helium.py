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

def bind_log(machine, A, B, name):
    f = calculate_loewy_friction(A, B)
    M_AB = mat_mul(A.matrix, B.matrix)
    # The extension class norm should not scale multiplicatively.
    # By taking the logarithm, we recover the additive extension phase.
    # We multiply by the vector space dimension (8) as suggested by the structural scaling.
    dim = 8
    energy = f * dim * math.log(frobenius_norm(M_AB))
    
    ext = ExtensionClass(name, energy)
    return machine.exact_sequence_reconstruction(A, B, ext)

machine = CategoricalMachine()

u_quarks = [machine.get_simple(3, color=f"c{i}") for i in range(12)]
d_quarks = [machine.get_simple(5, color=f"c{i}") for i in range(12)]
electrons = [machine.get_simple(2, color=f"e{i}") for i in range(2)]

p1_temp = bind_log(machine, u_quarks[0], u_quarks[1], "Strong (uu)")
p1 = bind_log(machine, p1_temp, d_quarks[0], "Strong (uud)")

p2_temp = bind_log(machine, u_quarks[2], u_quarks[3], "Strong (uu)")
p2 = bind_log(machine, p2_temp, d_quarks[1], "Strong (uud)")

n1_temp = bind_log(machine, u_quarks[4], d_quarks[2], "Strong (ud)")
n1 = bind_log(machine, n1_temp, d_quarks[3], "Strong (udd)")

n2_temp = bind_log(machine, u_quarks[5], d_quarks[4], "Strong (ud)")
n2 = bind_log(machine, n2_temp, d_quarks[5], "Strong (udd)")

alpha_temp1 = bind_log(machine, p1, p2, "Strong (pp)")
alpha_temp2 = bind_log(machine, alpha_temp1, n1, "Strong (ppn)")
helium_nucleus = bind_log(machine, alpha_temp2, n2, "Strong (ppnn)")

he_temp = bind_log(machine, helium_nucleus, electrons[0], "Electroweak")
helium_atom = bind_log(machine, he_temp, electrons[1], "Electroweak")

print(f"Proton Mass: {p1.mass:.2f} MeV")
print(f"Neutron Mass: {n1.mass:.2f} MeV")
print(f"Helium Nucleus Mass: {helium_nucleus.mass:.2f} MeV")
print(f"Helium Atom Mass: {helium_atom.mass:.2f} MeV")
