import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
import cmath
from unified_categorical_engine import CategoricalMachine, ExtensionClass

machine = CategoricalMachine()

# Overriding matrices for testing 3x3
m1 = [[complex(1,0), complex(0,1), complex(0,0)],
      [complex(0,-1), complex(2,0), complex(0,0)],
      [complex(0,0), complex(0,0), complex(3,0)]]

m2 = [[complex(0,0), complex(1,0), complex(0,0)],
      [complex(1,0), complex(0,0), complex(0,0)],
      [complex(0,0), complex(0,0), complex(1,0)]]

e1 = machine.get_simple(2)
e1.matrix = m1
e2 = machine.get_simple(3, color="blue")
e2.matrix = m2

ckm_3x3 = [[complex(1,0), complex(0,0), complex(0,0)],
           [complex(0,0), complex(1,0), complex(0,0)],
           [complex(0,0), complex(0,0), complex(1,0)]]

ext = ExtensionClass("Test 3x3", 0.0, matrix=ckm_3x3)
res = machine.exact_sequence_reconstruction(e1, e2, ext)

print("Original e1 signature:", e1.signature)
print("Original e2 signature:", e2.signature)
print("Result signature with 3x3 matrices phase shift:", res.signature)
print("Result matrix:", res.matrix)
