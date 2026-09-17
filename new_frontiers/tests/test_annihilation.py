import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine

machine = CategoricalMachine()
c = machine.get_simple(13)
anti_c = machine.get_simple(13, is_anti=True)

cc_bar = machine.exact_sequence_reconstruction(c, anti_c)

print(f"Meson: {cc_bar}")

decay_products = machine.decoupling_algorithm(cc_bar)
print("Decay products:")
for p in decay_products:
    print(f" - {p}")
