import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
import cmath
from unified_categorical_engine import CategoricalMachine, ExtensionClass

machine = CategoricalMachine()
e1 = machine.get_simple(2)
e2 = machine.get_simple(2, color="blue") # different color to bypass Pauli

print("e1 matrix:", e1.matrix)
print("e2 matrix:", e2.matrix)
ext = ExtensionClass("Test", 0.0, matrix=[[complex(1,0), complex(0,0)], [complex(0,0), complex(1,0)]])
res = machine.exact_sequence_reconstruction(e1, e2, ext)
print("Original e1 signature:", e1.signature)
print("Original e2 signature:", e2.signature)
print("Result signature (should be e1.sig * e2.sig if commute phase=0):", res.signature)
print("Expected signature without phase shift:", e1.signature * e2.signature)
