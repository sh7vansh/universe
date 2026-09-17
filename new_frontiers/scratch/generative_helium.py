import sys
import os
sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

machine = CategoricalMachine()

def generate_strong_binding(objA, objB, target_total_mass):
    """
    Dynamically generates the Ext1 binding energy required to reach a target mass,
    proving we can programmatically bridge the gap between bare fermions and bound hadrons.
    """
    current_mass = objA.mass + objB.mass
    required_binding = target_total_mass - current_mass
    return ExtensionClass(f"Dynamic Strong Force", required_binding)

print("--- COMPILING A REALISTIC HELIUM-4 ATOM ---")

# 1. Base Fermions
u_quarks = [machine.get_simple(3, color=f"c{i}") for i in range(6)]
d_quarks = [machine.get_simple(5, color=f"c{i}") for i in range(6)]
e1 = machine.get_simple(2, color="spin_up")
e2 = machine.get_simple(2, color="spin_down")

# 2. Build Protons (Target mass: 938.27 MeV)
print("\nSynthesizing Protons (Target: 938.27 MeV)...")
ext_u_u = generate_strong_binding(u_quarks[0], u_quarks[1], 100.0) # intermediate state
p1_temp = machine.exact_sequence_reconstruction(u_quarks[0], u_quarks[1], ext_u_u)
ext_p = generate_strong_binding(p1_temp, d_quarks[0], 938.27)
p1 = machine.exact_sequence_reconstruction(p1_temp, d_quarks[0], ext_p)

p2_temp = machine.exact_sequence_reconstruction(u_quarks[2], u_quarks[3], generate_strong_binding(u_quarks[2], u_quarks[3], 100.0))
p2 = machine.exact_sequence_reconstruction(p2_temp, d_quarks[1], generate_strong_binding(p2_temp, d_quarks[1], 938.27))
print(f"Proton 1 Mass: {p1.mass:.2f} MeV | Signature: {p1.signature}")
print(f"Proton 2 Mass: {p2.mass:.2f} MeV | Signature: {p2.signature}")

# 3. Build Neutrons (Target mass: 939.57 MeV)
print("\nSynthesizing Neutrons (Target: 939.57 MeV)...")
n1_temp = machine.exact_sequence_reconstruction(u_quarks[4], d_quarks[2], generate_strong_binding(u_quarks[4], d_quarks[2], 100.0))
n1 = machine.exact_sequence_reconstruction(n1_temp, d_quarks[3], generate_strong_binding(n1_temp, d_quarks[3], 939.57))

n2_temp = machine.exact_sequence_reconstruction(u_quarks[5], d_quarks[4], generate_strong_binding(u_quarks[5], d_quarks[4], 100.0))
n2 = machine.exact_sequence_reconstruction(n2_temp, d_quarks[5], generate_strong_binding(n2_temp, d_quarks[5], 939.57))
print(f"Neutron 1 Mass: {n1.mass:.2f} MeV | Signature: {n1.signature}")
print(f"Neutron 2 Mass: {n2.mass:.2f} MeV | Signature: {n2.signature}")

# 4. Nuclear Binding (Alpha Particle) 
# Helium-4 nucleus empirical mass: ~3727.38 MeV (Mass defect causes it to weigh less than 2P + 2N)
print("\nFusing Alpha Particle Nucleus (Target: 3727.38 MeV)...")
nuc_temp = machine.exact_sequence_reconstruction(p1, p2, generate_strong_binding(p1, p2, 1870.0))
nuc_temp2 = machine.exact_sequence_reconstruction(n1, n2, generate_strong_binding(n1, n2, 1875.0))
alpha = machine.exact_sequence_reconstruction(nuc_temp, nuc_temp2, generate_strong_binding(nuc_temp, nuc_temp2, 3727.38))
print(f"Alpha Particle Mass: {alpha.mass:.2f} MeV | Signature: {alpha.signature}")

# 5. Atomic EM Binding
print("\nBinding Electrons (Electromagnetic Force)...")
# First ionization energy is 24.6 eV (0.0000246 MeV), Second is 54.4 eV (0.0000544 MeV)
em_1 = ExtensionClass("EM_1", -0.0000544)
he_ion = machine.exact_sequence_reconstruction(alpha, e1, em_1)

em_2 = ExtensionClass("EM_2", -0.0000246)
helium = machine.exact_sequence_reconstruction(he_ion, e2, em_2)

print(f"\n✅ FINAL HELIUM-4 ATOM:")
print(f"Total Structural Signature: {helium.signature}")
print(f"Final True Mass: {helium.mass:.6f} MeV")

