import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine
machine = CategoricalMachine()
d = machine.get_simple(5)
anti_d = machine.get_simple(5, is_anti=True)
print(f"Down: {d.signature}")
print(f"Anti-Down: {anti_d.signature}")
