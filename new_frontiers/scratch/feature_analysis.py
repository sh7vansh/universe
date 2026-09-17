import sys
import os

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, ExtensionClass, mat_mul, mat_sub
import cmath

machine = CategoricalMachine()

def get_features(A, B):
    pA = abs(A.signature)
    pB = abs(B.signature)
    
    AB = mat_mul(A.matrix, B.matrix)
    BA = mat_mul(B.matrix, A.matrix)
    diff = mat_sub(AB, BA)
    comm = sum(abs(c) for r in diff for c in r)
    
    summ = [[AB[i][j] + BA[i][j] for j in range(len(AB[0]))] for i in range(len(AB))]
    anticomm = sum(abs(c) for r in summ for c in r)
    
    return [
        pA * pB,
        pA + pB,
        abs(pA - pB),
        comm,
        anticomm,
        1.0
    ]

u1 = machine.get_simple(3, color="red")
u2 = machine.get_simple(3, color="blue")
d1 = machine.get_simple(5, color="green")
d2 = machine.get_simple(5, color="red")

uu = machine.exact_sequence_reconstruction(u1, u2, ExtensionClass("UU", 0.0))
dd = machine.exact_sequence_reconstruction(d1, d2, ExtensionClass("DD", 0.0))

print("Features:")
print("U + U: ", get_features(u1, u2))
print("UU + D: ", get_features(uu, d1))
print("D + D: ", get_features(d1, d2))
print("DD + U: ", get_features(dd, u1))
