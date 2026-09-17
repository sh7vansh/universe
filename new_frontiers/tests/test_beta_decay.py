import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine

machine = CategoricalMachine()
u1 = machine.get_simple(3, color="red")
u2 = machine.get_simple(3, color="blue")
d1 = machine.get_simple(5, color="red")
d2 = machine.get_simple(5, color="blue")

proton = machine.exact_sequence_reconstruction(machine.exact_sequence_reconstruction(u1, u2), d1)
neutron = machine.exact_sequence_reconstruction(machine.exact_sequence_reconstruction(u1, d1), d2)

print(f"Neutron: {neutron}")
print(f"Proton: {proton}")

# Try partial decoupling of a proton from a neutron
residuals = machine.partial_decoupling(neutron, [proton.signature])
print("Residuals after extracting Proton:")
for r in residuals:
    print(f" - {r}")
