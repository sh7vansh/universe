import sys
import os
import unittest
import math

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, ExtensionClass, ALPHA

class LiquidDropCategoricalMachine(CategoricalMachine):
    """
    Subclass that applies the non-linear topological boundary curve (1.5 * alpha * A^(2/3))
    to the exact sequence friction count for color singlets.
    """
    def calculate_friction(self, A, B) -> float:
        def get_virtual_count(obj):
            if self.is_color_singlet(obj): return 0 
            return sum(len(ext.virtual_nodes) for ext in obj.extensions)
        
        optimal = len(A.factors) + len(B.factors)
        
        if self.is_color_singlet(A) and self.is_color_singlet(B):
            n_A = len(A.factors) / 3.0
            n_B = len(B.factors) / 3.0
            A_total = n_A + n_B
            
            # Topological boundary scaling for color singlets
            len_new_virtual = 1.0 + 1.5 * ALPHA * (A_total ** (2.0/3.0))
        else:
            len_new_virtual = self._get_shielded_length(A) + self._get_shielded_length(B)
            
        return (optimal + get_virtual_count(A) + get_virtual_count(B) + len_new_virtual) - optimal


class TestOxygenSynthesis(unittest.TestCase):
    def test_oxygen_16_synthesis(self):
        """
        Synthesizes Oxygen-16 using 4 Alpha particles and evaluates 
        accuracy using the liquid-drop topological boundary.
        """
        machine = LiquidDropCategoricalMachine()

        def create_nucleon(is_proton, suffix):
            if is_proton:
                u1 = machine.get_simple(3, color=f"red_p{suffix}")
                u2 = machine.get_simple(3, color=f"blue_p{suffix}")
                d1 = machine.get_simple(5, color=f"green_p{suffix}")
                diquark = machine.confinement_bind(u1, u2, f"DiQ_p{suffix}")
                return machine.confinement_bind(diquark, d1, f"Proton_{suffix}")
            else:
                u1 = machine.get_simple(3, color=f"red_n{suffix}")
                d1 = machine.get_simple(5, color=f"blue_n{suffix}")
                d2 = machine.get_simple(5, color=f"green_n{suffix}")
                diquark = machine.confinement_bind(u1, d1, f"DiQ_n{suffix}")
                return machine.confinement_bind(diquark, d2, f"Neutron_{suffix}")

        def build_alpha(index):
            p1 = create_nucleon(True, f"{index}_1")
            p2 = create_nucleon(True, f"{index}_2")
            n1 = create_nucleon(False, f"{index}_1")
            n2 = create_nucleon(False, f"{index}_2")

            if machine.kappa_residual is None:
                machine.calculate_residual_scale(p1.mass)

            he2 = machine.nuclear_bind(p1, p2, f"He-2_a{index}")
            he3 = machine.nuclear_bind(he2, n1, f"He-3_a{index}")
            return machine.nuclear_bind(he3, n2, f"Alpha_{index}")

        # Synthesize 4 Alpha particles
        a1 = build_alpha(1)
        a2 = build_alpha(2)
        a3 = build_alpha(3)
        a4 = build_alpha(4)

        # Nuclear fusion chain
        be8 = machine.nuclear_bind(a1, a2, "Beryllium-8")
        c12 = machine.nuclear_bind(be8, a3, "Carbon-12 Nucleus")
        o16_nucleus = machine.nuclear_bind(c12, a4, "Oxygen-16 Nucleus")

        self.assertEqual(len(o16_nucleus.factors), 48) # 16 nucleons * 3 quarks

        # Bind 8 electrons (1s, 2s, 2p)
        electron_states = [
            '1s_up', '1s_down', 
            '2s_up', '2s_down', 
            '2px_up', '2px_down', 
            '2py_up', '2py_down'
        ]

        atom = o16_nucleus
        for state in electron_states:
            e = machine.get_simple(2, color=state)
            # Geometrically derived Rydberg energy for atomic electron binding
            rydberg_energy = 0.5 * e.mass * (1.0 / 137.035999)**2
            em_force = ExtensionClass(f"Electromagnetic Binding {state}", -rydberg_energy)
            atom = machine.exact_sequence_reconstruction(atom, e, em_force)

        self.assertEqual(len(atom.factors), 56) # 48 quarks + 8 electrons
        self.assertEqual([f.name for f in atom.factors].count('Electron'), 8)

        # Verify against real Oxygen-16 mass (15.9949146 u * 931.494 MeV)
        real_o16_mass = 14899.169 
        
        # We expect the model mass to land within 2.0 MeV of the real mass
        self.assertTrue(abs(atom.mass - real_o16_mass) < 2.0)

if __name__ == '__main__':
    unittest.main()
