import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine
machine = CategoricalMachine()
u = machine.get_simple(3)
anti_d = machine.get_simple(5, is_anti=True)
pion = machine.exact_sequence_reconstruction(u, anti_d)
print(f"Pion signature: {pion.signature}")
