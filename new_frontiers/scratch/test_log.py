import sys
import os
import math
import cmath

sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, ExtensionClass, mat_mul

def frobenius_norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

def calculate_loewy_friction(objA, objB):
    optimal_length = len(objA.factors) + len(objB.factors)
    accumulated_virtual_nodes = sum(len(ext.virtual_nodes) for ext in objA.extensions + objB.extensions)
    new_virtual_nodes = len(objA.factors) + len(objB.factors)
    total_loewy_length = optimal_length + accumulated_virtual_nodes + new_virtual_nodes
    friction = total_loewy_length - optimal_length
    return friction

machine = CategoricalMachine()
u = machine.get_simple(3)
d = machine.get_simple(5)

# p1: uu
uu_matrix = mat_mul(u.matrix, u.matrix)
f1 = calculate_loewy_friction(u, u)

# p1: uud
uud_matrix = mat_mul(uu_matrix, d.matrix)
# wait, calculate_loewy_friction needs the object.
# Let's just create them.

def bind(A, B, name):
    f = calculate_loewy_friction(A, B)
    M_AB = mat_mul(A.matrix, B.matrix)
    # What if the energy is exactly friction * ||Ext1|| ?
    # But Ext1 is an exact sequence. 
    # What if energy is (f * vector_space_dim) * log(||M_AB||)?
    # Vector space dim = 8.
    energy = f * 8 * math.log(frobenius_norm(M_AB))
    ext = ExtensionClass(name, energy)
    return machine.exact_sequence_reconstruction(A, B, ext)

u1 = machine.get_simple(3)
u2 = machine.get_simple(3)
d1 = machine.get_simple(5)

uu = bind(u1, u2, "uu")
p = bind(uu, d1, "uud")

print("Proton Mass:", p.mass)

