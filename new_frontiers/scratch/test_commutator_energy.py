import sys
import os
import math

sys.path.append(os.path.abspath('src'))
from unified_categorical_engine import CategoricalMachine, ExtensionClass, mat_mul, mat_sub

def frobenius_norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

def calculate_loewy_friction(objA, objB):
    optimal_length = len(objA.factors) + len(objB.factors)
    accumulated_virtual_nodes = sum(len(ext.virtual_nodes) for ext in objA.extensions + objB.extensions)
    new_virtual_nodes = len(objA.factors) + len(objB.factors)
    total_loewy_length = optimal_length + accumulated_virtual_nodes + new_virtual_nodes
    friction = total_loewy_length - optimal_length
    return friction

def bind_comm(machine, A, B, name):
    f = calculate_loewy_friction(A, B)
    AB = mat_mul(A.matrix, B.matrix)
    BA = mat_mul(B.matrix, A.matrix)
    diff = mat_sub(AB, BA)
    
    norm_diff = frobenius_norm(diff)
    
    # What if energy is friction * norm_diff?
    energy = f * norm_diff
    ext = ExtensionClass(name, energy)
    return machine.exact_sequence_reconstruction(A, B, ext)

machine = CategoricalMachine()
u_quarks = [machine.get_simple(3, color=f"c{i}") for i in range(12)]
d_quarks = [machine.get_simple(5, color=f"c{i}") for i in range(12)]

p1_temp = bind_comm(machine, u_quarks[0], u_quarks[1], "Strong")
p1 = bind_comm(machine, p1_temp, d_quarks[0], "Strong")
print("Proton:", p1.mass)
