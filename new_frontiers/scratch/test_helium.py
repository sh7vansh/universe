import sys
import os
sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

machine = CategoricalMachine()

# To build Helium (2P, 2N), we need 6 Up quarks and 6 Down quarks in total.
# The engine enforces Pauli exclusion globally on the exact sequence. 
# They must all have unique state identifiers (colors).
u_quarks = [machine.get_simple(3, color=f"c{i}") for i in range(6)]
d_quarks = [machine.get_simple(5, color=f"c{i}") for i in range(6)]
e1 = machine.get_simple(2, color="spin_up")
e2 = machine.get_simple(2, color="spin_down")

strong = ExtensionClass("Strong", 10.0)

# Build Proton 1 (U U D)
p1_temp = machine.exact_sequence_reconstruction(u_quarks[0], u_quarks[1], strong)
p1 = machine.exact_sequence_reconstruction(p1_temp, d_quarks[0], strong)

# Build Proton 2 (U U D)
p2_temp = machine.exact_sequence_reconstruction(u_quarks[2], u_quarks[3], strong)
p2 = machine.exact_sequence_reconstruction(p2_temp, d_quarks[1], strong)

# Build Neutron 1 (U D D)
n1_temp = machine.exact_sequence_reconstruction(u_quarks[4], d_quarks[2], strong)
n1 = machine.exact_sequence_reconstruction(n1_temp, d_quarks[3], strong)

# Build Neutron 2 (U D D)
n2_temp = machine.exact_sequence_reconstruction(u_quarks[5], d_quarks[4], strong)
n2 = machine.exact_sequence_reconstruction(n2_temp, d_quarks[5], strong)

# Bind Nucleus
nucleus_temp1 = machine.exact_sequence_reconstruction(p1, p2, strong)
nucleus_temp2 = machine.exact_sequence_reconstruction(n1, n2, strong)
alpha = machine.exact_sequence_reconstruction(nucleus_temp1, nucleus_temp2, strong)

# Bind Electrons
he_ion = machine.exact_sequence_reconstruction(alpha, e1, ExtensionClass("EM", -0.001))
helium = machine.exact_sequence_reconstruction(he_ion, e2, ExtensionClass("EM", -0.001))

print(f"--- HELIUM ATOM ---")
print(f"Signature: {helium.signature}")
print(f"Mass: {helium.mass:.3f} MeV")

# Build H2 Molecule
# We can reuse p1, p2, e1, e2 since they have unique tags.
h1 = machine.exact_sequence_reconstruction(p1, e1, ExtensionClass("EM", -0.001))
h2 = machine.exact_sequence_reconstruction(p2, e2, ExtensionClass("EM", -0.001))
h2_mol = machine.exact_sequence_reconstruction(h1, h2, ExtensionClass("Covalent", -0.005))

print(f"\n--- H2 MOLECULE ---")
print(f"Signature: {h2_mol.signature}")
print(f"Mass: {h2_mol.mass:.3f} MeV")

