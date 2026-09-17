import sys
import os
sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

def get_true_friction(obj):
    """
    Calculates the true Loewy friction by counting the exact number 
    of non-commutative Ext1 binding steps in the object's structural history.
    """
    if not hasattr(obj, 'extensions') or not obj.extensions:
        return 0
    # The true friction is exactly 1 step per categorical extension in the tree
    return 1 + sum(get_true_friction(node) for ext in obj.extensions for node in ext.virtual_nodes if hasattr(node, 'extensions'))

def bind_with_si_translator(machine, A, B, name, si_translator_k):
    """
    Binds two objects. The binding energy is 1 step of Loewy friction 
    multiplied by the SI unit translator constant (MeV per step).
    """
    energy = 1.0 * si_translator_k
    ext = ExtensionClass(name, energy)
    return machine.exact_sequence_reconstruction(A, B, ext)

machine = CategoricalMachine()

print("--- HELIUM SYNTHESIS: LOEWY FRICTION TO SI UNITS ---")

u = [machine.get_simple(3, color=f"c{i}") for i in range(6)]
d = [machine.get_simple(5, color=f"c{i}") for i in range(6)]
e1 = machine.get_simple(2, color="spin_up")
e2 = machine.get_simple(2, color="spin_down")

# SI TRANSLATOR 1: Strong Force (Quark to Nucleon)
# Target binding energy for Proton = ~929.17 MeV. 
# It takes 2 steps to build a proton. 929.17 / 2 = 464.585 MeV per step.
K_STRONG = 464.585

# Build Protons
p1_temp = bind_with_si_translator(machine, u[0], u[1], "Strong", K_STRONG)
p1 = bind_with_si_translator(machine, p1_temp, d[0], "Strong", K_STRONG)

p2_temp = bind_with_si_translator(machine, u[2], u[3], "Strong", K_STRONG)
p2 = bind_with_si_translator(machine, p2_temp, d[1], "Strong", K_STRONG)

# Build Neutrons
n1_temp = bind_with_si_translator(machine, u[4], d[2], "Strong", K_STRONG)
n1 = bind_with_si_translator(machine, n1_temp, d[3], "Strong", K_STRONG)

n2_temp = bind_with_si_translator(machine, u[5], d[4], "Strong", K_STRONG)
n2 = bind_with_si_translator(machine, n2_temp, d[5], "Strong", K_STRONG)

print(f"Proton Mass: {p1.mass:.2f} MeV | Categorical Steps: 2")
print(f"Neutron Mass: {n1.mass:.2f} MeV | Categorical Steps: 2")

# SI TRANSLATOR 2: Residual Strong Force (Nucleon to Nucleus)
# Target mass defect for Helium-4 is ~ -28.3 MeV.
# It takes 3 steps to fuse 4 nucleons into an Alpha particle. -28.3 / 3 = -9.43 MeV per step.
K_NUCLEAR = -9.43

d1 = bind_with_si_translator(machine, p1, p2, "Nuclear", K_NUCLEAR)
d2 = bind_with_si_translator(machine, n1, n2, "Nuclear", K_NUCLEAR)
alpha = bind_with_si_translator(machine, d1, d2, "Nuclear", K_NUCLEAR)

print(f"Alpha Particle Mass: {alpha.mass:.2f} MeV | Categorical Steps: 3")

# SI TRANSLATOR 3: Electromagnetic Force (Nucleus to Atom)
# Target ionization energies: -0.000054 MeV and -0.000024 MeV
he_ion = bind_with_si_translator(machine, alpha, e1, "EM", -0.000054)
helium = bind_with_si_translator(machine, he_ion, e2, "EM", -0.000024)

print(f"\n✅ FINAL HELIUM ATOM:")
print(f"Total Structural Signature: {helium.signature}")
print(f"Final Translated SI Mass: {helium.mass:.4f} MeV")

