from mpmath import mp
mp.dps = 50

# ==============================================================================
# PURE UNIVERSE: A Dimensionless, Unitless Topological Ontology
#
# No kilograms, meters, seconds, electron-volts, or SI units exist here.
# Reality is modeled strictly as:
# 1. Level 0: Prime Factorization in the Grothendieck Ring (Identity)
# 2. Level 1 & 2: A3 Root Lattice Sphere-Packing Strain (Ext^3 Nuclear Geometry)
# 3. Level 3: U(1) Gauge Manifold Curvature (Electroweak Electronic Shells)
# 4. Level 4: Tor_1 Torsion Defects (Covalent Molecular Chemistry)
# ==============================================================================

# Global Dimensionless Topologies
ALPHA = (9.0 / (16.0 * (mp.pi ** 3))) * ((mp.pi / 120.0) ** 0.25)  # Wyler's constant
PHI = (1.0 + mp.sqrt(5.0)) / 2.0                                    # Golden ratio
NOISE = mp.log(2 * mp.pi)                                           # Boundary Shannon noise

# Ontological Primes (Level 0 Generators)
ELECTRON = 2
UP_QUARK = 3
DOWN_QUARK = 5


class PureAtom:
    """
    An isolated atomic state in the Grothendieck ring.
    The identity is a prime composite integer.
    The mass is an illusion: it is simply the manifold strain of packing
    A = Z + N spheres into a 3D A3 root lattice with boundary curvature.
    """
    def __init__(self, name: str, Z: int, N: int):
        self.name = name
        self.Z = Z
        self.N = N
        self.A = Z + N

        # LEVEL 0: ONTOLOGICAL ROOT (The Gödel Fraction)
        # Exact position in the free abelian group on primes {2, 3, 5}
        self.godel = (ELECTRON**Z) * (UP_QUARK**(2*Z + N)) * (DOWN_QUARK**(Z + 2*N))

        # LEVEL 1 & 2: THE A3 LATTICE DEFECT (Nuclear Manifold Strain)
        # Volume rank of A packed spheres in FCC (A3) lattice:
        self.volume = (6.0 / mp.pi) * self.A if self.A > 0 else mp.mpf(0)

        # THE EXT^3 SPATIAL LIMIT:
        # A local simplex cannot exceed dim=3 in spatial geometry.
        dim = min(self.A - 1, 3)
        boundary_exp = (dim - 1.0) / dim if dim > 0 else mp.mpf(0)
        self.surface = (NOISE ** 2) * (self.A ** boundary_exp) if self.A > 0 else mp.mpf(0)

        # Kissing Number Repulsion (Coulomb obstruction on A3 lattice)
        self.kissing = (12.0 * ALPHA) * Z * (Z - 1) / (self.A ** (1.0 / 3.0)) if self.A > 0 else mp.mpf(0)

        # Isospin Orthogonality Defect (Neutron-Proton asymmetry)
        self.asymmetry = 2.0 * mp.sqrt(2.0) * ((N - Z) ** 2) / self.A if self.A > 0 else mp.mpf(0)

        # Net nuclear strain (difference between flat Euclidean grid and curved packing)
        self.nuclear_strain = self.volume - self.surface - self.kissing - self.asymmetry

        # LEVEL 3: ELECTROWEAK U(1) CURVATURE (Electronic Shell Strain)
        # Pure geometric ratio of the orbital sheath (dimensionless Thomas-Fermi scale)
        self.electronic_strain = -0.5 * (ALPHA ** 2) * (Z ** (7.0 / 3.0)) if Z > 0 else mp.mpf(0)

        # Total intrinsic strain of the atom
        self.total_strain = self.nuclear_strain + self.electronic_strain

    def __repr__(self):
        return f"PureAtom({self.name}, Z={self.Z}, N={self.N})"


class PureBond:
    """
    Tor_1 Torsion Defect:
    When two atoms share an electron pair, their individual Ext^3 nuclear lattices
    do NOT merge (A_tot does not fuse).
    Instead, an abelian torsion product Tor_1(Z_A, Z_B) bridges their electronic boundaries.
    The defect is purely dimensionless, governed by Wyler's coupling ALPHA^2 and PHI.
    """
    def __init__(self, atom_a: PureAtom, atom_b: PureAtom, bond_order: int = 1):
        self.atom_a = atom_a
        self.atom_b = atom_b
        self.bond_order = bond_order

        # Harmonic coordinate radius of the shared valence zone
        mu_z = mp.mpf(atom_a.Z * atom_b.Z) / mp.mpf(atom_a.Z + atom_b.Z)

        # Dimensionless Tor_1 torsion strain:
        # Each shared pair produces a localized negative strain in the U(1) sheath
        self.torsion_strain = - (self.bond_order / PHI) * (0.5 * (ALPHA ** 2)) * (mu_z ** (1.0 / 3.0))

    def __repr__(self):
        return f"PureBond({self.atom_a.name}-{self.atom_b.name}, order={self.bond_order})"


class PureMolecule:
    """
    A compound state in the Grothendieck ring.
    - Identity: Multiplicative product of atomic Gödel integers.
    - Nuclear Volume: Strictly additive (no nuclear fusion occurs; nuclei are disjoint).
    - Manifold Strain: Sum of atomic intrinsic strains + Tor_1 torsion defects.
    """
    def __init__(self, name: str, atoms: list[PureAtom], bonds: list[PureBond]):
        self.name = name
        self.atoms = atoms
        self.bonds = bonds

        # Level 0: Multiplication in the Grothendieck ring
        self.godel = 1
        for a in atoms:
            self.godel *= a.godel

        # Volumes and strains remain disjoint sums perturbed only by Tor_1
        self.nuclear_volume = sum(a.volume for a in atoms)
        self.nuclear_strain = sum(a.nuclear_strain for a in atoms)
        self.electronic_strain = sum(a.electronic_strain for a in atoms)
        self.torsion_strain = sum(b.torsion_strain for b in bonds)
        self.total_strain = self.nuclear_strain + self.electronic_strain + self.torsion_strain

    def print_spec(self):
        g_str = str(self.godel)
        if len(g_str) > 28:
            g_str = f"{g_str[:10]}...{g_str[-10:]} ({len(g_str)} digits)"

        print(f"==================================================")
        print(f"Molecule            : {self.name}")
        print(f"Gödel Integer (ID)  : {g_str}")
        print(f"Constituent Atoms   : {', '.join(a.name for a in self.atoms)}")
        print(f"Bonds (Tor_1 Orders): {[b.bond_order for b in self.bonds]}")
        print(f"Nuclear Volume Rank : {float(self.nuclear_volume):.6f}")
        print(f"Nuclear Strain      : {float(self.nuclear_strain):.6f}")
        print(f"Electronic Strain   : {float(self.electronic_strain):.8e}")
        print(f"Tor_1 Torsion Defect: {float(self.torsion_strain):.8e}")
        print(f"Total Net Strain    : {float(self.total_strain):.6f}")
        print(f"==================================================")


def pure_universe(Z: int, N: int):
    """Backwards-compatible helper returning (godel_id, volume, total_strain)."""
    atom = PureAtom(f"Atom({Z},{N})", Z, N)
    return atom.godel, atom.volume, atom.total_strain


if __name__ == '__main__':
    print("=== PURE ISOLATED ATOMS (NO UNITS) ===")
    print(f"{'Atom':<12} | {'State (Gödel ID)':<25} | {'Volume Rank':>15} | {'Manifold Strain'}")
    print("-" * 80)
    for name, z, n in [
        ("Hydrogen-1", 1, 0),
        ("Helium-4", 2, 2),
        ("Carbon-12", 6, 6),
        ("Oxygen-16", 8, 8),
        ("Zinc-64", 30, 34)
    ]:
        atom = PureAtom(name, z, n)
        g_str = str(atom.godel) if len(str(atom.godel)) < 22 else f"{str(atom.godel)[:8]}...{str(atom.godel)[-8:]}"
        print(f"{name:<12} | {g_str:<25} | {float(atom.volume):>15.6f} | {float(atom.total_strain):>20.6f}")

    print("\n=== PURE MOLECULES (TOR_1 TORSION DEFECTS) ===")
    H = PureAtom("H", 1, 0)
    O = PureAtom("O", 8, 8)
    C = PureAtom("C", 6, 6)
    N = PureAtom("N", 7, 7)

    # 1. Dihydrogen (Single bond)
    h2 = PureMolecule("H2", [H, H], [PureBond(H, H, 1)])
    h2.print_spec()

    # 2. Water (Two single bonds)
    h2o = PureMolecule("H2O", [O, H, H], [PureBond(O, H, 1), PureBond(O, H, 1)])
    h2o.print_spec()

    # 3. Dinitrogen (Triple bond)
    n2 = PureMolecule("N2", [N, N], [PureBond(N, N, 3)])
    n2.print_spec()

    # 4. Carbon Dioxide (Two double bonds)
    co2 = PureMolecule("CO2", [C, O, O], [PureBond(C, O, 2), PureBond(C, O, 2)])
    co2.print_spec()
