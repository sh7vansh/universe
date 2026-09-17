import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, mat_mul, mat_sub
machine = CategoricalMachine()
u = machine.get_simple(3)
d = machine.get_simple(5)
pA = abs(u.signature)
pB = abs(d.signature)
AB = mat_mul(u.matrix, d.matrix)
BA = mat_mul(d.matrix, u.matrix)
diff = mat_sub(AB, BA)
comm = sum(abs(c) for r in diff for c in r)
print("u, d comm:", comm)
print("4|pa - pb|:", 4 * abs(pA - pB))
