import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, ExtensionClass
machine = CategoricalMachine()
u = machine.get_simple(3, color="red")  # Up Quark
anti_d = machine.get_simple(5, is_anti=True, color="red")  # Anti-Down
pion_ext = ExtensionClass("Strong Force (Pion)", 130.0)
pion = machine.exact_sequence_reconstruction(u, anti_d, pion_ext)
print(f"Pion: {pion}")
print(f"Pion Signature: {pion.signature}")
print(f"Pion Spin: {pion.spin}")

# Pentaquark: uudcc_bar
d = machine.get_simple(5, color="green")
c = machine.get_simple(13, color="red")
anti_c = machine.get_simple(13, is_anti=True, color="blue")
u2 = machine.get_simple(3, color="blue")
penta_ext = ExtensionClass("Strong Force (Pentaquark)", 4000.0)
uu = machine.exact_sequence_reconstruction(u, u2)
uud = machine.exact_sequence_reconstruction(uu, d)
uudc = machine.exact_sequence_reconstruction(uud, c)
penta = machine.exact_sequence_reconstruction(uudc, anti_c, penta_ext)
print(f"Pentaquark: {penta}")
print(f"Pentaquark Signature: {penta.signature}")
print(f"Pentaquark Spin: {penta.spin}")

