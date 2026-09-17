import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

machine = CategoricalMachine()
u1 = machine.get_simple(3, color="red")
u2 = machine.get_simple(3, color="blue")
d = machine.get_simple(5, color="green")
c = machine.get_simple(13, color="red")
anti_c = machine.get_simple(13, is_anti=True, color="blue")

u_u = machine.exact_sequence_reconstruction(u1, u2)
u_u_d = machine.exact_sequence_reconstruction(u_u, d)
u_u_d_c = machine.exact_sequence_reconstruction(u_u_d, c)
pentaquark = machine.exact_sequence_reconstruction(u_u_d_c, anti_c)

print(f"Pentaquark: {pentaquark}")
print(f"Mass: {pentaquark.mass}")

decay_products = machine.decoupling_algorithm(pentaquark)
print("Decay products:")
for p in decay_products:
    print(f" - {p}")

total_decay_mass = sum(p.mass for p in decay_products)
print(f"Total decay mass: {total_decay_mass}")
