import unittest
from core.molecular_engine import CategoricalChemistryEngine, parse_formula

class TestBaseline(unittest.TestCase):
    def test_h2o(self):
        engine = CategoricalChemistryEngine()
        formula = "H2O"
        comps = parse_formula(formula)
        atoms_list = []
        isolated_mass = 0.0
        for sym, count in comps:
            for i in range(count):
                tag = f"{sym.upper()}{i+1}"
                atom = engine.atomic_engine(sym, tag)
                atoms_list.append(atom)
                isolated_mass += atom.mass

        molecule = engine.molecular_bind(atoms_list, formula)
        bond_defect = molecule.mass - isolated_mass
        self.assertLess(bond_defect, 0.0)

if __name__ == "__main__":
    unittest.main()
