from mpmath import mp
mp.dps = 50

# The Universe has no units. Only geometry and prime numbers.

# Global Topologies
ALPHA = (9.0 / (16.0 * (mp.pi ** 3))) * ((mp.pi / 120.0) ** 0.25)
PHI = (1.0 + mp.sqrt(5.0)) / 2.0
NOISE = mp.log(2 * mp.pi)

# Pure Primes
ELECTRON = 2
UP_QUARK = 3
DOWN_QUARK = 5

def pure_universe(Z: int, N: int):
    A = Z + N
    if A == 0: return 0, 0, 0

    # LEVEL 0: ONTOLOGICAL ROOT (The Gödel Fraction)
    # The absolute identity of the object in the Grothendieck ring.
    # No mass, no energy. Just its prime factorization state.
    identity = (ELECTRON**Z) * (UP_QUARK**(2*Z + N)) * (DOWN_QUARK**(Z + 2*N))

    # LEVEL 1 & 2: THE TOPOLOGICAL DEFECT (Lattice Strain)
    # Instead of calculating 'mass defect in MeV', we calculate the dimensionless strain.
    # Physics calls this "Binding Energy", but mathematically it is just the difference 
    # between the ideal flat volume and the curled boundary of the A3 lattice.

    volume = (6.0 / mp.pi) * A

    # THE EXT^3 SPATIAL LIMIT
    # A local simplex cannot exceed 3 dimensions in our universe.
    # At A=4 (Helium-4), the 3D space is full. Heavy atoms are forced to crystallize.
    dim = min(A - 1, 3)
    boundary_exp = (dim - 1.0) / dim if dim > 0 else 0.0
    surface = (NOISE ** 2) * (A ** boundary_exp)

    kissing_repulsion = (12.0 * ALPHA) * Z * (Z - 1) / (A ** (1.0 / 3.0))
    asymmetry = 2.0 * mp.sqrt(2.0) * ((N - Z) ** 2) / A

    # The total topological defect of the tensor product (binding)
    manifold_strain = volume - surface - kissing_repulsion - asymmetry

    # LEVEL 3: ELECTROWEAK SCALING (Dimensionless Rydberg)
    # Instead of -13.6 eV, it's just the pure geometric ratio
    orbital_strain = -0.5 * (ALPHA ** 2) * (Z ** (7.0 / 3.0))

    total_strain = manifold_strain + orbital_strain

    return identity, volume, total_strain

if __name__ == '__main__':
    print(f"{'Atom':<12} | {'State (Gödel ID)':<25} | {'Volume Rank':>15} | {'Manifold Strain (Defect)'}")
    print("-" * 80)
    for name, z, n in [
        ("Hydrogen-1", 1, 0),
        ("Helium-4", 2, 2),
        ("Carbon-12", 6, 6),
        ("Oxygen-16", 8, 8),
        ("Zinc-64", 30, 34)
    ]:
        godel, vol, strain = pure_universe(z, n)
        g_str = str(godel) if len(str(godel)) < 22 else f"{str(godel)[:8]}...{str(godel)[-8:]}"
        print(f"{name:<12} | {g_str:<25} | {vol:>15.6f} | {strain:>20.6f}")
