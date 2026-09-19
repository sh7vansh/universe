from mpmath import mp
mp.dps = 100

import copy
from typing import List, Optional, Union
from dataclasses import dataclass, field
from fractions import Fraction

def round_complex(z, decimals=10):
    return z

def mat_mul(m1: List[List[complex]], m2: List[List[complex]]) -> List[List[complex]]:
    n = len(m1)
    m = len(m2[0])
    p = len(m2)
    result = [[complex(0, 0)] * m for _ in range(n)]
    for i in range(n):
        for j in range(m):
            for k in range(p):
                result[i][j] += m1[i][k] * m2[k][j]
    return result

def mat_sub(m1: List[List[complex]], m2: List[List[complex]]) -> List[List[complex]]:
    return [[m1[i][j] - m2[i][j] for j in range(len(m1[0]))] for i in range(len(m1))]

# Universal Geometric Constants
MU_0 = 1.0
WYLER_ALPHA = (9.0 / (16.0 * (mp.pi ** 3))) * ((mp.pi / 120.0) ** 0.25)
ALPHA_INV = 1.0 / WYLER_ALPHA
ALPHA = 1.0 / ALPHA_INV
G_A = 7.0 ** (1.0 / 8.0)  # Axial vector coupling (Strange Prime rooted to Gluon space)
PHI = (1.0 + mp.sqrt(5.0)) / 2.0  # The Golden Ratio

def universal_mass(p: int, gauge_friction: float) -> float:
    """
    The Universal Mass Equation: m(p) = \\mu_0 * ((p - 1)/2 + F_gauge)
    Partitions every particle into a universal base geometry (topological genus)
    and its specific environmental resistance (gauge friction).
    For heavy quarks, F_gauge is built recursively by exponentiating 
    the frictions of lower generations.
    """
    if p in (0, 1):
        return 0.0
    bare_mass = (p - 1) / 2.0
    return MU_0 * (bare_mass + gauge_friction)

# Geometrically Derived Gauge Frictions
F_E = 1.5 * ALPHA + ALPHA**2
F_U = 2.0 / mp.sqrt(3)
F_D = 8.0 / 3.0

# Higher Generation Gauge Frictions
# Maps the Strange Quark. QED Vacuum shielded by Proton signature 45.
F_STRANGE = ALPHA_INV - 45.0  

F_CHARM = (mp.sqrt(3))**13  # SU(3) root lattice geometry raised to prime identifier 13.
F_BOTTOM = F_STRANGE * (ALPHA_INV / 3.0)  # Strange friction scaled by QED vacuum anchor.
F_TOP = F_STRANGE ** F_D  # Generation 2 Strange friction raised to the Generation 1 Down friction

# Lepton geometric derivations
M_E = universal_mass(2, F_E)
# Muon is the Electron scaled by QED dipole, plus inverse Golden Ratio self-energy.
M_MUON = (M_E * 1.5 * ALPHA_INV) + (MU_0 / PHI)
F_MUON = (M_MUON / MU_0) - (11 - 1) / 2.0

# Tau is the QED vacuum scaled by Gen 2 prime 13, minus one Down Quark self-energy.
M_D = universal_mass(5, F_D)
M_TAU = (13.0 * ALPHA_INV * MU_0) - M_D
F_TAU = (M_TAU / MU_0) - (17 - 1) / 2.0

class PauliExclusionError(Exception):
    pass

@dataclass
class SimpleObject:
    """
    A fundamental fermion. Uses prime numbers as unique identifiers instead of physical mass.
    """
    name: str
    identifier: int 
    mass: float
    spin: float
    color: Optional[str] = None
    is_anti: bool = False

SIMPLE_OBJECTS = {
    0: SimpleObject("Void", 0, 0.0, 0.0),
    1: SimpleObject("Photon", 1, 0.0, 1.0),
    2: SimpleObject("Electron", 2, universal_mass(2, F_E), 0.5),
    3: SimpleObject("Up Quark", 3, universal_mass(3, F_U), 0.5),
    5: SimpleObject("Down Quark", 5, universal_mass(5, F_D), 0.5),
    7: SimpleObject("Strange Quark", 7, universal_mass(7, F_STRANGE), 0.5),
    11: SimpleObject("Muon", 11, universal_mass(11, F_MUON), 0.5),
    13: SimpleObject("Charm Quark", 13, universal_mass(13, F_CHARM), 0.5),
    17: SimpleObject("Tau", 17, universal_mass(17, F_TAU), 0.5),
    19: SimpleObject("Bottom Quark", 19, universal_mass(19, F_BOTTOM), 0.5),
    23: SimpleObject("Top Quark", 23, universal_mass(23, F_TOP), 0.5)
}

@dataclass
class ExtensionClass:
    """
    A Yoneda extension class in the Ext1 tower. Stores binding energy, CP violation matrices, and virtual state memory.
    """
    name: str
    binding_energy: float 
    matrix: Optional[List[List[complex]]] = None
    virtual_nodes: List[SimpleObject] = field(default_factory=list)

@dataclass
class GrothendieckObject:
    """
    A composite particle in the Grothendieck group K_0. Identified by complex signature Z = Magnitude * e^(i * pi * Spin).
    """
    signature: complex
    mass: float
    factors: List[SimpleObject] = field(default_factory=list)
    extensions: List[ExtensionClass] = field(default_factory=list)
    matrix: List[List[complex]] = field(default_factory=lambda: [[complex(1,0), complex(0,0)], [complex(0,0), complex(1,0)]])

    @property
    def spin(self) -> float:
        if abs(self.signature) < 1e-9:
            return 0.0
        raw_spin = mp.phase(self.signature) / mp.pi
        rounded_spin = round(raw_spin, 5)
        if abs(rounded_spin) < 1e-9:
            return 0.0
        return rounded_spin

    def __str__(self):
        comp = [f.name for f in self.factors]
        if abs(self.signature) > 1e-9:
            real_part = f"{self.signature.real:g}" if abs(self.signature.real) > 1e-9 else "0"
            imag_part = f"{self.signature.imag:+g}j" if abs(self.signature.imag) > 1e-9 else ""
            if real_part == "0" and imag_part:
                sig_str = imag_part.lstrip('+')
            elif imag_part == "":
                sig_str = real_part
            else:
                sig_str = f"{real_part}{imag_part}"
        else:
            sig_str = "0"
        return f"GrothendieckObject(Signature={sig_str}, Mass={self.mass:.3f} MeV, Spin={self.spin}, Composition={comp})"

class CategoricalMachine:
    """
    Runs categorical tracking, binding, and decay. Uses discrete algebraic operations, not continuous fields.
    
    Args:
        pure_math_mode (bool): If True, skips physical mass scaling and outputs raw integer friction.
    """
    # ==========================================
    # 1. CORE / BASE METHODS
    # ==========================================
    def __init__(self, pure_math_mode: bool = False):
        self.generators = SIMPLE_OBJECTS
        self.pure_math_mode = pure_math_mode
        
        # First-principles base inputs
        self.m_u = universal_mass(3, F_U)       # Geometrically Derived Up Quark (MeV)
        self.m_d = universal_mass(5, F_D)       # Geometrically Derived Down Quark (MeV)
        self.f_pi = F_STRANGE * MU_0            # Pion Decay Constant derived algebraically (alpha^-1 - 45)
        
        # Mathematical vacuum density
        # Calculates chiral condensate vacuum density from number theory and QED constants.
        # X = 1/2 * pi * ln(2*pi) * alpha^-1 * sqrt((0.5 + 1.5*alpha + alpha^2) * mu_0^2)
        geometric_scalar = 0.5 + 1.5 * ALPHA + ALPHA**2
        vacuum_density = 0.5 * mp.pi * mp.log(2 * mp.pi) * ALPHA_INV * mp.sqrt(geometric_scalar * MU_0**2)
        self.chiral_condensate = -(vacuum_density)**3
        
        # Strong force geometry
        # Calculates residual nuclear scale from the Deuteron Boundary (Riemann noise degraded by the electromagnetic boundary).
        
        # 1. GMOR CONFINEMENT EQUATION
        self.m_pi = mp.sqrt(- ((self.m_u + self.m_d) * self.chiral_condensate) / (self.f_pi**2))

        # 1.5 COLOR-MAGNETIC SPIN-SPIN INTERACTION
        # Distributes the confinement meson scale across SU(3) color permutations.
        self.kappa_spin = self.m_pi / 9.0
        self.kappa_em = 11.0 / 3.0  # Geometrically derived lepton-color bridge (p=11 / N_c=3)

        if not self.pure_math_mode:
            self.kappa_confinement = self.m_pi
            self.kappa_residual = None 
        else:
            self.kappa_confinement = 1.0
            self.kappa_residual = 1.0

    def get_simple(self, prime: int, is_anti: bool = False, color: Optional[str] = None) -> GrothendieckObject:
        """
        Creates a fundamental particle as a GrothendieckObject. Sets reciprocal magnitude fractions for antimatter.
        """
        if prime not in self.generators:
            simp = SimpleObject(f"Unknown Simple ({prime})", prime, 0.0, 0.5, color, is_anti)
        else:
            base_simp = self.generators[prime]
            mass = 0.0 if self.pure_math_mode else base_simp.mass
            name = base_simp.name if prime in (0, 1) else (f"Anti-{base_simp.name}" if is_anti else base_simp.name)
            simp = SimpleObject(name, prime, mass, base_simp.spin, color, is_anti)
            
        val = prime if not is_anti else -prime
        matrix = [
            [complex(val, 0), complex(0, 1)],
            [complex(0, -1), complex(-val, 0)]
        ] if prime != 0 else [
            [complex(1, 0), complex(0, 0)],
            [complex(0, 0), complex(1, 0)]
        ]
            
        if is_anti:
            mag = 0 if prime == 0 else Fraction(1, prime)
            sig = round_complex((float(mag) * mp.exp(1j * mp.pi * simp.spin))) if mag != 0 else 0j
            return GrothendieckObject(signature=sig, mass=simp.mass, factors=[simp], extensions=[], matrix=matrix)
        else:
            sig = round_complex((float(prime) * mp.exp(1j * mp.pi * simp.spin))) if prime != 0 else 0j
            return GrothendieckObject(signature=sig, mass=simp.mass, factors=[simp], extensions=[], matrix=matrix)

    def is_color_singlet(self, obj: GrothendieckObject) -> bool:
        """Categorical SU(3) encapsulation equation."""
        net = {'red': 0, 'green': 0, 'blue': 0}
        for f in obj.factors:
            if f.color:
                base_color = f.color.split('_')[0]
                val = -1 if f.is_anti else 1
                if 'red' in base_color: net['red'] += val
                elif 'green' in base_color: net['green'] += val
                elif 'blue' in base_color: net['blue'] += val
        return (len(obj.factors) > 0) and (net['red'] == net['green'] == net['blue'])

    def _get_shielded_length(self, obj: GrothendieckObject) -> int:
        if self.is_color_singlet(obj):
            return 1
        return len(obj.factors)

    # ==========================================
    # 2. BASE RECONSTRUCTION & FRICTION
    # ==========================================
    def exact_sequence_reconstruction(self, A: GrothendieckObject, B: GrothendieckObject, ext: Optional[ExtensionClass] = None) -> GrothendieckObject:
        """
        Reconstructs the short exact sequence. Multiplies complex signatures and enforces Pauli Exclusion.
        Applies extension matrices for geometric phase shifts.
        """
        for f1 in A.factors:
            for f2 in B.factors:
                if (f1.spin % 1) != 0.0:
                    if (f1.identifier == f2.identifier and
                        f1.spin == f2.spin and
                        f1.color == f2.color and
                        f1.is_anti == f2.is_anti):
                        raise PauliExclusionError(f"Pauli Exclusion Principle violation: Identical fermions {f1.name} (color={f1.color}) cannot occupy the same state.")
                        
        sig_C = round_complex(A.signature * B.signature)
        mass_C = A.mass + B.mass
        
        ext_list = list(A.extensions) + list(B.extensions)
        matrix_C = mat_mul(A.matrix, B.matrix)
        
        if ext is not None:
            ext_copy = copy.deepcopy(ext)
            if not ext_copy.virtual_nodes:
                ext_copy.virtual_nodes = list(A.factors) + list(B.factors)
            
            if ext_copy.matrix is not None:
                M_A = A.matrix
                M_B = B.matrix
                AB = mat_mul(M_A, M_B)
                BA = mat_mul(M_B, M_A)
                diff = mat_sub(AB, BA)
                
                val = complex(1, 0)
                found = False
                for r in diff:
                    for c in r:
                        if abs(c) >= 1e-9:
                            val = c
                            found = True
                            break
                    if found: break
                    
                phase_shift = mp.phase(val)
                sig_C = round_complex(sig_C * (1.0 * mp.exp(1j * phase_shift)))
                matrix_C = mat_mul(ext_copy.matrix, AB)
                
            mass_C += ext_copy.binding_energy
            ext_list.append(ext_copy)
            
        return GrothendieckObject(
            signature=sig_C,
            mass=mass_C,
            factors=list(A.factors) + list(B.factors),
            extensions=ext_list,
            matrix=matrix_C
        )

    def calculate_friction(self, A: GrothendieckObject, B: GrothendieckObject) -> float:
        """Categorical friction equation."""
        def get_virtual_count(obj):
            if self.is_color_singlet(obj): return 0 
            return sum(len(ext.virtual_nodes) for ext in obj.extensions)
        
        optimal = len(A.factors) + len(B.factors)
        
        if self.is_color_singlet(A) and self.is_color_singlet(B):
            def get_Z_N(obj):
                if not obj.factors: return 0, 0
                u = sum(1 for f in obj.factors if f.identifier == 3)
                d = sum(1 for f in obj.factors if f.identifier == 5)
                return round((2*u - d)/3.0), round((2*d - u)/3.0)
                
            def geom_friction(Z, N):
                """
                Calculates the Loewy length discrepancy of the composite Ext^n complex.
                This algebra matches the classical Liquid Drop Model at macroscopic limits.
                Rank acts as volume. Boundary degradation acts as surface tension.
                Phase interference acts as Coulomb repulsion. Parity violation acts as asymmetry.
                Pairing bonus acts as topological singlet pairing. Cohomological closure acts as magic shells.
                """
                A_tot = Z + N
                if A_tot <= 1: return 0.0
                
                # 1. RANK (VOLUME)
                # Derived from the density of square-free integers. Scaled by the 1D phase circumference as states project into spatial volume.
                square_free_density_projection = 6.0 / mp.pi
                
                # 2. BOUNDARY DEGRADATION (SURFACE TENSION)
                # Evaluates the Loewy length discrepancy using the Nucleon Condensate
                if hasattr(self, 'nucleon_condensate'):
                    rank = square_free_density_projection * A_tot
                    boundary_degradation = self.nucleon_condensate * (A_tot ** (2.0/3.0))
                else:
                    rank = square_free_density_projection * A_tot
                    boundary_degradation = mp.sqrt(5.0) * (A_tot ** (2.0/3.0))
                    
                # 3. PHASE INTERFERENCE (COULOMB)
                # Distributes the electromagnetic offset over the 3D Topological Kissing Number (12). Local exact sequences in 3D embedding max out at 12 adjacent states. Continuous physics uses a Z^(4/3) Pauli exchange volume. The Ext^n tower operates on discrete prime factors, so exact sequence discrete permutations govern phase interference.
                topological_kissing_number = 12.0
                phase_interference = (topological_kissing_number * ALPHA) * Z * (Z - 1) / (A_tot ** (1.0/3.0)) if A_tot > 0 else 0.0
                
                # 4. PARITY VIOLATION & SU(4) WIGNER ALIGNMENT
                # The SU(2) Casimir invariant generates the quadratic asymmetry and the Wigner resonance penalty for breaking exact N=Z symmetry.
                complex_orthogonality = 2.0 * mp.sqrt(2.0)
                parity_violation = complex_orthogonality * ((N - Z) ** 2) / A_tot
                su4_wigner = complex_orthogonality * abs(N - Z) / A_tot
                
                # 5. COHOMOLOGICAL CLOSURE (MAGIC SHELLS)
                cohomological_closure = 0.0
                
                # Generates magic numbers from SU(3) Pronic shells and topological phase shifts.
                magic_numbers = set()
                cumulative = 0
                for n in range(1, 8):
                    pronic = n * (n + 1)
                    cumulative += pronic
                    if n < 4:
                        magic_numbers.add(cumulative)
                    else:
                        prev_pronic = (n - 1) * n
                        magic_numbers.add(cumulative - prev_pronic)
                        
                # 6. TOPOLOGICAL PAIRING, CHIRAL CURRENTS, & SU(4) CLUSTERING
                # One paired state shields one quantum of Riemann Viscosity.
                pairing_bonus = 0.0
                chiral_current_bonus = 0.0
                alpha_cluster_bonus = 0.0
                if A_tot > 0:
                    riemann_viscosity = 0.5
                    
                    # 6a. Spin Pairing & Chiral Currents
                    if Z % 2 == 0 and N % 2 == 0:
                        pairing_bonus = riemann_viscosity / (A_tot ** 0.5)
                        # SU(4) Alpha Clustering and Cohomological Closure are mutually exclusive.
                        if Z == N and (Z not in magic_numbers):
                            alpha_cluster_bonus = (riemann_viscosity * 2.0) / (A_tot ** (1.0/3.0))
                    elif Z % 2 != 0 and N % 2 != 0:
                        pairing_bonus = -riemann_viscosity / (A_tot ** 0.5)
                    elif Z % 2 != 0 and N % 2 == 0:
                        # An unpaired proton creates an electromagnetic spin-orbit topological current on the boundary.
                        chiral_current_bonus = (riemann_viscosity * ALPHA) / (A_tot ** (1.0/3.0))
                
                volumetric_dampener = 1.0 / (A_tot ** (1.0/3.0)) if A_tot > 0 else 1.0
                ext_tower_limit = mp.pi / 4.0
                
                if Z in magic_numbers: cohomological_closure += ext_tower_limit * volumetric_dampener
                if N in magic_numbers: cohomological_closure += ext_tower_limit * volumetric_dampener
                
                return rank - boundary_degradation - phase_interference - parity_violation - su4_wigner + pairing_bonus + alpha_cluster_bonus + chiral_current_bonus + cohomological_closure

            Z_A, N_A = get_Z_N(A)
            Z_B, N_B = get_Z_N(B)
            
            f_A = geom_friction(Z_A, N_A)
            f_B = geom_friction(Z_B, N_B)
            f_C = geom_friction(Z_A + Z_B, N_A + N_B)
            
            # Return the incremental friction needed for the new composite
            return f_C - (f_A + f_B)
        else:
            len_new_virtual = self._get_shielded_length(A) + self._get_shielded_length(B)
            return (optimal + get_virtual_count(A) + get_virtual_count(B) + len_new_virtual) - optimal

    def calculate_entanglement(self, A: GrothendieckObject, B: GrothendieckObject) -> float:
        import math
        mag_A = Fraction(abs(A.signature)).limit_denominator(1000000000000000)
        mag_B = Fraction(abs(B.signature)).limit_denominator(1000000000000000)
        shared_matter = math.gcd(mag_A.numerator, mag_B.numerator)
        shared_anti = math.gcd(mag_A.denominator, mag_B.denominator)
        if shared_matter == 1 and shared_anti == 1: return 0.0
        return float(shared_matter * shared_anti)

    # ==========================================
    # 3. QUARKS (CONFINEMENT & STRONG FORCE)
    # ==========================================
    def confinement_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        """Binds simple objects using the GMOR mass scale."""
        delta_L = self.calculate_friction(A, B)
        
        # Color-Magnetic Spin-Spin Interaction (applied only within confinement boundary)
        spin_scalar = 0.0
        if hasattr(self, 'kappa_spin'):
            # Calculate standard parallel scalar
            parallel_scalar = 0.0
            for f1 in A.factors:
                for f2 in B.factors:
                    z1 = (1.0 * mp.exp(1j * mp.pi * f1.spin))
                    z2 = (1.0 * mp.exp(1j * mp.pi * f2.spin))
                    parallel_scalar += (z1 * z2.conjugate()).real
            
            # Calculate anti-parallel scalar (if B flips its spin)
            anti_scalar = 0.0
            for f1 in A.factors:
                for f2 in B.factors:
                    z1 = (1.0 * mp.exp(1j * mp.pi * f1.spin))
                    z2 = (1.0 * mp.exp(1j * mp.pi * (-f2.spin)))
                    anti_scalar += (z1 * z2.conjugate()).real
                    
            # The system seeks the lowest energy state. Flips B before binding if anti-aligning drops the mass.
            if anti_scalar < parallel_scalar:
                spin_scalar = anti_scalar
                B.signature = B.signature.conjugate()
                for f in B.factors:
                    f.spin = -f.spin
            else:
                spin_scalar = parallel_scalar
        
        def get_charge(f):
            if f.identifier == 3: return (2.0/3.0) * (-1 if f.is_anti else 1)
            if f.identifier == 5: return (-1.0/3.0) * (-1 if f.is_anti else 1)
            return 0.0
            
        electrostatic_scalar = 0.0
        for f1 in A.factors:
            for f2 in B.factors:
                electrostatic_scalar += get_charge(f1) * get_charge(f2)
                
        binding_energy = (delta_L * self.kappa_confinement) + (self.kappa_spin * spin_scalar if hasattr(self, 'kappa_spin') else 0.0)
        if hasattr(self, 'kappa_em'):
            binding_energy += self.kappa_em * electrostatic_scalar
        
        ext = ExtensionClass(name, binding_energy=binding_energy)
        ext.virtual_nodes = list(A.factors) + list(B.factors)
        return self.exact_sequence_reconstruction(A, B, ext)

    # ==========================================
    # 4. NUCLEI (RESIDUAL STRONG FORCE)
    # ==========================================
    def calculate_residual_scale(self, emergent_nucleon_mass: float):
        """
        Calculates the nuclear friction scalar (kappa_residual) from Riemann Vacuum Noise 
        and the fine-structure constant. Replaces Goldberger-Treiman and Yukawa. 
        The Deuteron Binding Energy acts as the geometric boundary.
        """
        if self.pure_math_mode:
            self.kappa_residual = 1.0
            return
            
        noise = mp.log(2 * mp.pi)
        viscosity = 0.5
        
        # 1. Nucleon Condensate (Deuteron Boundary)
        # Evaluates pure topological noise disrupted by electromagnetic boundaries.
        self.nucleon_condensate = (noise ** 2) * (1.0 - (1.0 / (viscosity ** 2)) / mp.sqrt(ALPHA_INV)) * MU_0
        
        # 2. Kappa Residual (Base Categorical Friction Scalar)
        # Projects the localized Nucleon Condensate across 4D spacetime geometry to define the global residual friction scale.
        self.kappa_residual = - (self.nucleon_condensate * (1.0 / (viscosity ** 2)))

    def deep_vacuum_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        base_friction = self.calculate_friction(A, B)
        total_friction = base_friction 
        n = 1
        current_correction = base_friction * float(WYLER_ALPHA)
        while abs(current_correction) > 1e-15:
            phase = (-1) ** n
            total_friction += phase * current_correction
            n += 1
            current_correction *= float(WYLER_ALPHA)
        binding_energy = total_friction * float(self.kappa_residual) if hasattr(self, 'kappa_residual') and self.kappa_residual else total_friction
        ext = ExtensionClass(name, binding_energy=binding_energy)
        ext.virtual_nodes = list(A.factors) + list(B.factors)
        return self.exact_sequence_reconstruction(A, B, ext)

    def nuclear_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        """Builds nuclei with accurate negative mass defects using the infinite Ext tower."""
        if self.kappa_residual is None:
            raise ValueError("Must calculate residual scale from a bound nucleon first.")
        
        # Routes the macroscopic geometry through the infinite Ext^n vacuum solver.
        return self.deep_vacuum_bind(A, B, name)

    # ==========================================
    # 5. ATOMS (ELECTROWEAK)
    # ==========================================
    def electroweak_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str, binding_energy: float = -0.0000136) -> GrothendieckObject:
        """Builds atoms via electroweak interaction with a specified mass defect."""
        ext = ExtensionClass(name, binding_energy=binding_energy)
        ext.virtual_nodes = list(A.factors) + list(B.factors)
        return self.exact_sequence_reconstruction(A, B, ext)

    # ==========================================
    # 6. DECAY & DECOUPLING
    # ==========================================
    def decoupling_algorithm(self, obj: GrothendieckObject) -> List[GrothendieckObject]:
        """
        Simulates particle decay with cellular filtration. Factors the signature magnitude into primes 
        to find the constituent fundamental particles.
        """
        magnitude = abs(obj.signature)
        if magnitude < 1e-9: return [self.get_simple(0)]
        mag_frac = Fraction(magnitude).limit_denominator(1000000000000000)
        if mag_frac == 1: return [self.get_simple(1)]
        
        def factorize(n: int) -> List[int]:
            factors, d = [], 2
            while d * d <= n:
                while (n % d) == 0:
                    factors.append(d)
                    n //= d
                d += 1
            if n > 1: factors.append(n)
            return factors
            
        num_factors = factorize(mag_frac.numerator)
        den_factors = factorize(mag_frac.denominator)
        
        available_factors = list(obj.factors)
        decoupled_objects = []
        for f in num_factors:
            color = None
            for i, af in enumerate(available_factors):
                if af.identifier == f and not af.is_anti:
                    color = af.color
                    available_factors.pop(i)
                    break
            decoupled_objects.append(self.get_simple(f, is_anti=False, color=color))
            
        for f in den_factors:
            color = None
            for i, af in enumerate(available_factors):
                if af.identifier == f and af.is_anti:
                    color = af.color
                    available_factors.pop(i)
                    break
            decoupled_objects.append(self.get_simple(f, is_anti=True, color=color))
            
        return decoupled_objects

    def partial_decoupling(self, obj: GrothendieckObject, target_signatures: List[complex]) -> List[GrothendieckObject]:
        current_sig = obj.signature
        current_mag = Fraction(abs(current_sig)).limit_denominator(1000000000000000)
        decoupled_objects = []
        available_factors = list(obj.factors)
        
        def factorize(n: int) -> List[int]:
            factors, d = [], 2
            while d * d <= n:
                while (n % d) == 0:
                    factors.append(d)
                    n //= d
                d += 1
            if n > 1: factors.append(n)
            return factors
            
        for target in target_signatures:
            target_val = target if isinstance(target, complex) else complex(float(target))
            target_mag = Fraction(abs(target_val)).limit_denominator(1000000000000000)
            
            if target_mag != 0 and current_mag.numerator % target_mag.numerator == 0 and current_mag.denominator % target_mag.denominator == 0:
                current_mag = current_mag / target_mag
                current_sig = round_complex(current_sig / target_val)
                
                target_factors = []
                for f in factorize(target_mag.numerator):
                    for i, af in enumerate(available_factors):
                        if af.identifier == f and not af.is_anti:
                            target_factors.append(available_factors.pop(i))
                            break
                for f in factorize(target_mag.denominator):
                    for i, af in enumerate(available_factors):
                        if af.identifier == f and af.is_anti:
                            target_factors.append(available_factors.pop(i))
                            break
                
                comp = GrothendieckObject(signature=target_val, mass=sum(f.mass for f in target_factors), factors=target_factors)
                decoupled_objects.append(comp)
                
        remaining_simple = self.decoupling_algorithm(GrothendieckObject(signature=current_sig, mass=sum(f.mass for f in available_factors), factors=available_factors))
        decoupled_objects.extend(remaining_simple)
        return decoupled_objects


def run_simulation(pure_math_mode: bool = False):
    machine = CategoricalMachine(pure_math_mode=pure_math_mode)
    
    mode_text = "PURE MATH MODE" if pure_math_mode else "STANDARD MODEL"
    print(f"--- FIRST-PRINCIPLES CATEGORICAL {mode_text} ---")
    
    u1 = machine.get_simple(3, color="red_p1")
    u2 = machine.get_simple(3, color="blue_p1")
    d1 = machine.get_simple(5, color="green_p1")
    e = machine.get_simple(2)
    
    print("\n1. Bootstrapping Nucleon Mass (Confinement / GMOR):")
    diquark = machine.confinement_bind(u1, u2, "Diquark")
    proton = machine.confinement_bind(diquark, d1, "Proton")
    print(f"   Synthesized Proton: {proton}")
    
    print("\n2. Bootstrapping Nuclear Physics (Nucleon Condensate):")
    machine.calculate_residual_scale(proton.mass)
    print(f"   Nucleon Condensate (Deuteron Boundary): {machine.nucleon_condensate:.4f} MeV")
    print(f"   Base Residual Friction (Kappa): {machine.kappa_residual:.4f} MeV")
    
    print("\n3. Synthesizing Helium-4:")
    p2 = machine.confinement_bind(machine.confinement_bind(machine.get_simple(3, color="red_p2"), machine.get_simple(3, color="blue_p2"), "DiQ"), machine.get_simple(5, color="green_p2"), "Proton 2")
    n1 = machine.confinement_bind(machine.confinement_bind(machine.get_simple(3, color="red_n1"), machine.get_simple(5, color="blue_n1"), "DiQ"), machine.get_simple(5, color="green_n1"), "Neutron 1")
    n2 = machine.confinement_bind(machine.confinement_bind(machine.get_simple(3, color="red_n2"), machine.get_simple(5, color="blue_n2"), "DiQ"), machine.get_simple(5, color="green_n2"), "Neutron 2")
    
    he2 = machine.nuclear_bind(proton, p2, "He-2")
    he3 = machine.nuclear_bind(he2, n1, "He-3")
    he4 = machine.nuclear_bind(he3, n2, "Helium-4")
    print(f"   Synthesized Helium-4: {he4}")
    print(f"   Total Mass Defect: {he4.mass - (2*proton.mass + 2*n1.mass):.2f} MeV")

    print("\n4. Electroweak Binding (Hydrogen Atom):")
    hydrogen = machine.electroweak_bind(proton, e, "Hydrogen Atom")
    print(f"   Synthesized Hydrogen Atom: {hydrogen}")

    print("\n5. Decoupling Algorithm (Transfinite Filtration):")
    decoupled = machine.decoupling_algorithm(hydrogen)
    print(f"   Extracted {len(decoupled)} simple composition factors natively from the Hydrogen signature.")
    
    print("\n6. Weak Force & CP Violation (Virtual State Memory):")
    charm = machine.get_simple(13, color="red")
    anti_charm = machine.get_simple(13, is_anti=True, color="red")
    
    ckm_matrix = [
        [complex(0.974, 0), complex(0.225, 0)],
        [complex(-0.225, 0), complex(0.974, 0)]
    ]
    weak_force = ExtensionClass("Weak Force (W-Boson)", 0.0, matrix=ckm_matrix)
    
    j_psi = machine.exact_sequence_reconstruction(charm, anti_charm, weak_force)
    print(f"   Synthesized J/Psi (Charm + Anti-Charm): {j_psi}")
    
    decoupled_jpsi = machine.decoupling_algorithm(j_psi)
    print(f"   Decoupled J/Psi into Photons (Magnitude {abs(j_psi.signature)}): {[str(obj) for obj in decoupled_jpsi]}")
    print(f"   Virtual State Memory logged in Extension: {[n.name for n in j_psi.extensions[0].virtual_nodes]}")

if __name__ == "__main__":
    import sys
    pure_math = "--pure-math" in sys.argv
    run_simulation(pure_math_mode=pure_math)
