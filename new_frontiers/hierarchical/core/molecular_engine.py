from typing import List
import copy
from mpmath import mp
from core.quantum_engine import GrothendieckObject, SimpleObject, CONFIG
from core.atomic_engine import synthesize_element_core

class TorClass:
    def __init__(self, name: str, dissociation_energy_ev: float, atoms: List[GrothendieckObject]):
        self.name = name
        self.defect_mev = -(dissociation_energy_ev / 1e6) 
        self.atoms = atoms

class Molecule(GrothendieckObject):
    def __init__(self, name: str, signature: complex, mass: float):
        super().__init__(signature, mass)
        self.name = name
        self.atoms: List[GrothendieckObject] = []
        self.torsion_bonds: List[TorClass] = []

def molecular_tensor_product(A: GrothendieckObject, B: GrothendieckObject, bond_name: str, bond_ev: float) -> Molecule:
    defect_mev = -(bond_ev / 1e6)
    mol_mass = A.mass + B.mass + defect_mev
    mol_sig = A.signature * B.signature

    mol = Molecule(bond_name, mol_sig, mol_mass)

    atoms_A = A.atoms if isinstance(A, Molecule) else [A]
    atoms_B = B.atoms if isinstance(B, Molecule) else [B]
    mol.atoms = atoms_A + atoms_B

    bonds_A = A.torsion_bonds if isinstance(A, Molecule) else []
    bonds_B = B.torsion_bonds if isinstance(B, Molecule) else []

    new_bond = TorClass(bond_name, bond_ev, [A, B])
    mol.torsion_bonds = bonds_A + bonds_B + [new_bond]

    return mol

if __name__ == '__main__':
    H1 = synthesize_element_core("Hydrogen-A", 1, 0)
    H2 = synthesize_element_core("Hydrogen-B", 1, 0)
    O  = synthesize_element_core("Oxygen", 8, 8)

    print(f"Isolated H Mass: {H1.mass:,.6f} MeV")
    print(f"Isolated O Mass: {O.mass:,.6f} MeV\n")

    h2_gas = molecular_tensor_product(H1, H2, "H-H Covalent", 4.52)
    print(f"--- {h2_gas.name} ---")
    print(f"Atoms: {len(h2_gas.atoms)}")
    print(f"Bonds (Tor_1): {len(h2_gas.torsion_bonds)}")
    print(f"Mass: {h2_gas.mass:,.6f} MeV")
    print(f"Molecular Defect: {h2_gas.torsion_bonds[-1].defect_mev * 1e6:.2f} eV\n")

    hydroxyl = molecular_tensor_product(O, H1, "O-H Bond 1", 4.77)
    water = molecular_tensor_product(hydroxyl, H2, "O-H Bond 2", 4.77)

    print(f"--- Water (H2O) ---")
    print(f"Atoms: {len(water.atoms)}")
    print(f"Bonds (Tor_1): {len(water.torsion_bonds)}")
    print(f"Mass: {water.mass:,.6f} MeV")
    total_bond_ev = sum(b.defect_mev for b in water.torsion_bonds) * 1e6
    print(f"Total Covalent Defect: {total_bond_ev:.2f} eV")
