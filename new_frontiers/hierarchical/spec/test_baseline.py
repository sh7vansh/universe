import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'core')))
from molecular_engine import CategoricalChemistryEngine, parse_formula

def test_h2o():
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
    bond_defect_ev = bond_defect * 1_000_000
    print(f"H2O Bond Defect eV: {bond_defect_ev:.2f}")

test_h2o()
