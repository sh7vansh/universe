import sys
import os
import math
import copy

sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, ExtensionClass, mat_mul, mat_sub

def frobenius_norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

def calculate_loewy_friction(objA, objB):
    optimal_length = len(objA.factors) + len(objB.factors)
    accumulated_virtual_nodes = sum(len(ext.virtual_nodes) for ext in objA.extensions + objB.extensions)
    new_virtual_nodes = len(objA.factors) + len(objB.factors)
    total_loewy_length = optimal_length + accumulated_virtual_nodes + new_virtual_nodes
    friction = total_loewy_length - optimal_length
    return friction

def bind_algebraic(machine, A, B, name):
    # The binding energy emerges purely from the categorical algebra!
    # Option 1: || M_A * M_B ||
    # Option 2: friction * || M_A * M_B ||
    # Option 3: friction * Vector Space Dimension (which is 8 for 2x2 complex matrices)
    
    # We will use the geometric norm of the Yoneda Extension Class Ext1
    # which physically manifests as the matrix product M_A M_B
    M_AB = mat_mul(A.matrix, B.matrix)
    ext1_norm = frobenius_norm(M_AB)
    
    # To incorporate the transfinite cellular filtration depth:
    friction = calculate_loewy_friction(A, B)
    
    # Emerging binding energy = friction * ||Ext1||
    emergent_energy = friction * ext1_norm
    
    ext = ExtensionClass(name, emergent_energy)
    return machine.exact_sequence_reconstruction(A, B, ext)

machine = CategoricalMachine()

# 1. Fundamental Generators
u_quarks = [machine.get_simple(3, color=f"c{i}") for i in range(12)]
d_quarks = [machine.get_simple(5, color=f"c{i}") for i in range(12)]
electrons = [machine.get_simple(2, color=f"e{i}") for i in range(2)]

# 2. Nucleosynthesis of 2 Protons
p1_temp = bind_algebraic(machine, u_quarks[0], u_quarks[1], "Strong (uu)")
p1 = bind_algebraic(machine, p1_temp, d_quarks[0], "Strong (uud)")

p2_temp = bind_algebraic(machine, u_quarks[2], u_quarks[3], "Strong (uu)")
p2 = bind_algebraic(machine, p2_temp, d_quarks[1], "Strong (uud)")

# 3. Nucleosynthesis of 2 Neutrons
n1_temp = bind_algebraic(machine, u_quarks[4], d_quarks[2], "Strong (ud)")
n1 = bind_algebraic(machine, n1_temp, d_quarks[3], "Strong (udd)")

n2_temp = bind_algebraic(machine, u_quarks[5], d_quarks[4], "Strong (ud)")
n2 = bind_algebraic(machine, n2_temp, d_quarks[5], "Strong (udd)")

# 4. Helium Nucleus (Alpha Particle)
alpha_temp1 = bind_algebraic(machine, p1, p2, "Strong (pp)")
alpha_temp2 = bind_algebraic(machine, alpha_temp1, n1, "Strong (ppn)")
helium_nucleus = bind_algebraic(machine, alpha_temp2, n2, "Strong (ppnn)")

# 5. Helium Atom
he_temp = bind_algebraic(machine, helium_nucleus, electrons[0], "Electroweak")
helium_atom = bind_algebraic(machine, he_temp, electrons[1], "Electroweak")

print(f"Proton Mass: {p1.mass:.2f} MeV")
print(f"Neutron Mass: {n1.mass:.2f} MeV")
print(f"Helium Nucleus Mass: {helium_nucleus.mass:.2f} MeV")
print(f"Helium Atom Mass: {helium_atom.mass:.2f} MeV")
