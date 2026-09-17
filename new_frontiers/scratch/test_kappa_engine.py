import sys
import os
import math

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, GrothendieckObject, ExtensionClass, mat_mul

class KappaCategoricalMachine(CategoricalMachine):
    def __init__(self):
        super().__init__()
        self.kappa = self._compute_kappa()

    def _compute_kappa(self) -> float:
        up = self.get_simple(3)
        anti_down = self.get_simple(5, is_anti=True)
        m_pion = mat_mul(up.matrix, anti_down.matrix)
        return math.sqrt(sum(abs(c)**2 for r in m_pion for c in r))

    def calculate_friction(self, A: GrothendieckObject, B: GrothendieckObject) -> int:
        optimal_length = len(A.factors) + len(B.factors)
        accumulated_virtual = sum(len(ext.virtual_nodes) for ext in A.extensions + B.extensions)
        new_virtual = len(A.factors) + len(B.factors)
        
        total_length = optimal_length + accumulated_virtual + new_virtual
        return total_length - optimal_length

    def strong_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        friction = self.calculate_friction(A, B)
        energy = friction * self.kappa
        ext = ExtensionClass(name, binding_energy=energy)
        return self.exact_sequence_reconstruction(A, B, ext)

def run_test():
    machine = KappaCategoricalMachine()
    
    print(f"Base Kappa (Emergent Pion Invariant): {machine.kappa:.4f} MeV\n")
    
    u1 = machine.get_simple(3, color="red")
    u2 = machine.get_simple(3, color="blue")
    d = machine.get_simple(5, color="green")
    
    print(f"Up 1: {u1}")
    print(f"Up 2: {u2}")
    print(f"Down: {d}\n")
    
    # 1. Bind UU
    u_u = machine.strong_bind(u1, u2, "Strong Force (UU)")
    print(f"Synthesized U-U Diquark:\n{u_u}\n")
    
    # 2. Bind UU with D
    proton = machine.strong_bind(u_u, d, "Strong Force (UU-D)")
    print(f"Synthesized Proton:\n{proton}\n")

if __name__ == "__main__":
    run_test()
