import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

machine = CategoricalMachine()
charm = machine.get_simple(13, color="red")
anti_charm = machine.get_simple(13, is_anti=True, color="red")

ckm_matrix = [
    [complex(0.974, 0), complex(0.225, 0)],
    [complex(-0.225, 0), complex(0.974, 0)]
]
weak_force = ExtensionClass("Weak Force", 0.0, matrix=ckm_matrix)

j_psi = machine.exact_sequence_reconstruction(charm, anti_charm, weak_force)
print("J/Psi signature:", j_psi.signature)
print("Virtual nodes:", [n.name for n in j_psi.extensions[0].virtual_nodes])
