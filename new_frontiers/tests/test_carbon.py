import sys
import os
import unittest

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, ExtensionClass

class TestCarbonSynthesis(unittest.TestCase):
    def test_carbon_12_synthesis(self):
        """
        Synthesizes Carbon-12 using the Triple-Alpha process to follow 
        physically accurate geometric clustering.
        """
        machine = CategoricalMachine(pure_math_mode=False)

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

        alpha1 = build_alpha(1)
        alpha2 = build_alpha(2)
        alpha3 = build_alpha(3)

        be8 = machine.nuclear_bind(alpha1, alpha2, "Beryllium-8")
        carbon_nucleus = machine.nuclear_bind(be8, alpha3, "Carbon-12 Nucleus")

        self.assertTrue(carbon_nucleus.mass > 0)
        self.assertEqual(len(carbon_nucleus.factors), 36)

        electron_states = ['1s_up', '1s_down', '2s_up', '2s_down', '2px_up', '2px_down']

        atom = carbon_nucleus
        for state in electron_states:
            e = machine.get_simple(2, color=state)
            # Geometrically derived Rydberg energy for atomic electron binding
            rydberg_energy = 0.5 * e.mass * (1.0 / 137.035999)**2
            em_force = ExtensionClass(f"Electromagnetic Binding {state}", -rydberg_energy)
            atom = machine.exact_sequence_reconstruction(atom, e, em_force)

        expected_unbound_mass = carbon_nucleus.mass + sum(f.mass for f in atom.factors if f.name == 'Electron')
        self.assertTrue(atom.mass < expected_unbound_mass)
        self.assertEqual(len(atom.factors), 42)

        electron_names = [f.name for f in atom.factors]
        self.assertIn('Electron', electron_names)
        self.assertEqual(electron_names.count('Electron'), 6)

if __name__ == '__main__':
    unittest.main()
