import sys
import os
sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

def calculate_loewy_friction(objA, objB):
    optimal_length = len(objA.factors) + len(objB.factors)
    accumulated_virtual_nodes = sum(len(ext.virtual_nodes) for ext in objA.extensions + objB.extensions)
    new_virtual_nodes = len(objA.factors) + len(objB.factors)
    total_loewy_length = optimal_length + accumulated_virtual_nodes + new_virtual_nodes
    friction = total_loewy_length - optimal_length
    return friction

def bind_with_loewy(machine, A, B, name, coupling_constant):
    friction = calculate_loewy_friction(A, B)
    energy = friction * coupling_constant
    ext = ExtensionClass(name, energy)
    return machine.exact_sequence_reconstruction(A, B, ext)

machine = CategoricalMachine()

u_quarks = [machine.get_simple(3, color=f"c{i}") for i in range(6)]
d_quarks = [machine.get_simple(5, color=f"c{i}") for i in range(6)]
e1 = machine.get_simple(2, color="spin_up")
e2 = machine.get_simple(2, color="spin_down")

# Proton bare mass = 9.1. Target binding = 929.17
# Total friction for a 3-part composite is 2 + 5 = 7.
# 929.17 / 7 = 132.738
STRONG_K = 132.738

p1_temp = bind_with_loewy(machine, u_quarks[0], u_quarks[1], "Strong", STRONG_K)
p1 = bind_with_loewy(machine, p1_temp, d_quarks[0], "Strong", STRONG_K)

n1_temp = bind_with_loewy(machine, u_quarks[4], d_quarks[2], "Strong", STRONG_K)
n1 = bind_with_loewy(machine, n1_temp, d_quarks[3], "Strong", STRONG_K)

print(f"Proton Mass: {p1.mass:.2f} MeV")
print(f"Neutron Mass: {n1.mass:.2f} MeV")
