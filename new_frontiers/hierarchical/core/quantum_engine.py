from mpmath import mp
mp.dps = 100

import copy
from typing import List, Optional
from dataclasses import dataclass, field
from fractions import Fraction

def mat_mul(m1: List[List[complex]], m2: List[List[complex]]) -> List[List[complex]]:
    return [[sum(m1[i][k] * m2[k][j] for k in range(len(m2))) for j in range(len(m2[0]))] for i in range(len(m1))]

@dataclass
class PhysicsConfig:
    mu_0: float = 1.0
    wyler_alpha: float = (9.0 / (16.0 * (mp.pi ** 3))) * ((mp.pi / 120.0) ** 0.25)
    alpha_inv: float = 1.0 / ((9.0 / (16.0 * (mp.pi ** 3))) * ((mp.pi / 120.0) ** 0.25))
    alpha: float = ((9.0 / (16.0 * (mp.pi ** 3))) * ((mp.pi / 120.0) ** 0.25))
    g_a: float = 7.0 ** (1.0 / 8.0)
    phi: float = (1.0 + mp.sqrt(5.0)) / 2.0

CONFIG = PhysicsConfig()

def universal_mass(p: int, gauge_friction: float) -> float:
    if p in (0, 1):
        return 0.0
    return CONFIG.mu_0 * ((p - 1) / 2.0 + gauge_friction)

F_E = 1.5 * CONFIG.alpha + CONFIG.alpha**2
F_U = 2.0 / mp.sqrt(3)
F_D = 8.0 / 3.0
F_STRANGE = CONFIG.alpha_inv - 45.0  
F_CHARM = (mp.sqrt(3))**13
F_BOTTOM = F_STRANGE * (CONFIG.alpha_inv / 3.0)
F_TOP = F_STRANGE ** F_D

M_E = universal_mass(2, F_E)
M_MUON = (M_E * 1.5 * CONFIG.alpha_inv) + (CONFIG.mu_0 / CONFIG.phi)
F_MUON = (M_MUON / CONFIG.mu_0) - (11 - 1) / 2.0
M_D = universal_mass(5, F_D)
M_TAU = (13.0 * CONFIG.alpha_inv * CONFIG.mu_0) - M_D
F_TAU = (M_TAU / CONFIG.mu_0) - (17 - 1) / 2.0

class PauliExclusionError(Exception):
    pass

@dataclass
class SimpleObject:
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
    name: str
    binding_energy: float 
    matrix: Optional[List[List[complex]]] = None
    virtual_nodes: List[SimpleObject] = field(default_factory=list)

@dataclass
class GrothendieckObject:
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
        return 0.0 if abs(rounded_spin) < 1e-9 else rounded_spin

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

def get_Z_N(obj: GrothendieckObject):
    if not obj.factors: return 0, 0
    u = sum(1 for f in obj.factors if f.identifier == 3)
    d = sum(1 for f in obj.factors if f.identifier == 5)
    return round((2*u - d)/3.0), round((2*d - u)/3.0)

def geom_friction(Z: int, N: int, nucleon_condensate: Optional[float] = None) -> float:
    A_tot = Z + N
    if A_tot <= 1: return 0.0

    square_free_density_projection = 6.0 / mp.pi
    rank = square_free_density_projection * A_tot
    boundary_degradation = (nucleon_condensate if nucleon_condensate is not None else mp.sqrt(5.0)) * (A_tot ** (2.0/3.0))
    topological_kissing_number = 12.0
    phase_interference = (topological_kissing_number * CONFIG.alpha) * Z * (Z - 1) / (A_tot ** (1.0/3.0)) if A_tot > 0 else 0.0
    complex_orthogonality = 2.0 * mp.sqrt(2.0)
    parity_violation = complex_orthogonality * ((N - Z) ** 2) / A_tot
    su4_wigner = complex_orthogonality * abs(N - Z) / A_tot

    cohomological_closure = 0.0
    magic_numbers = set()
    cumulative = 0
    for n in range(1, 8):
        pronic = n * (n + 1)
        cumulative += pronic
        magic_numbers.add(cumulative if n < 4 else cumulative - (n - 1) * n)

    pairing_bonus = 0.0
    alpha_cluster_bonus = 0.0
    chiral_current_bonus = 0.0
    if A_tot > 0:
        riemann_viscosity = 0.5
        if Z % 2 == 0 and N % 2 == 0:
            pairing_bonus = riemann_viscosity / (A_tot ** 0.5)
            if Z == N and (Z not in magic_numbers):
                alpha_cluster_bonus = (riemann_viscosity * 2.0) / (A_tot ** (1.0/3.0))
        elif Z % 2 != 0 and N % 2 != 0:
            pairing_bonus = -riemann_viscosity / (A_tot ** 0.5)
        elif Z % 2 != 0 and N % 2 == 0:
            chiral_current_bonus = (riemann_viscosity * CONFIG.alpha) / (A_tot ** (1.0/3.0))

    volumetric_dampener = 1.0 / (A_tot ** (1.0/3.0)) if A_tot > 0 else 1.0
    ext_tower_limit = mp.pi / 4.0

    if (Z in magic_numbers) and (N not in magic_numbers):
        cohomological_closure += ext_tower_limit * volumetric_dampener
    elif (N in magic_numbers) and (Z not in magic_numbers):
        cohomological_closure += ext_tower_limit * volumetric_dampener
    elif (Z in magic_numbers) and (N in magic_numbers):
        # Doubly-magic closed shells: zero valence pairing, self-contained topological closure
        pairing_bonus = 0.0
        cohomological_closure = 0.0

    return rank - boundary_degradation - phase_interference - parity_violation - su4_wigner + pairing_bonus + alpha_cluster_bonus + chiral_current_bonus + cohomological_closure

class CategoricalMachine:
    def __init__(self):
        self.generators = SIMPLE_OBJECTS
        self.m_u = universal_mass(3, F_U)
        self.m_d = universal_mass(5, F_D)
        self.f_pi = F_STRANGE * CONFIG.mu_0

        geometric_scalar = 0.5 + 1.5 * CONFIG.alpha + CONFIG.alpha**2
        vacuum_density = 0.5 * mp.pi * mp.log(2 * mp.pi) * CONFIG.alpha_inv * mp.sqrt(geometric_scalar * CONFIG.mu_0**2)
        self.chiral_condensate = -(vacuum_density)**3

        self.m_pi = mp.sqrt(- ((self.m_u + self.m_d) * self.chiral_condensate) / (self.f_pi**2))
        self.kappa_spin = self.m_pi / 9.0
        self.kappa_em = 11.0 / 3.0
        self.kappa_confinement = self.m_pi

        # Pure geometric residual nuclear scale
        noise = mp.log(2 * mp.pi)
        viscosity = 0.5
        self.nucleon_condensate = (noise ** 2) * (1.0 - (1.0 / (viscosity ** 2)) / mp.sqrt(CONFIG.alpha_inv))
        self.kappa_residual = - (self.nucleon_condensate * (1.0 / (viscosity ** 2))) * CONFIG.mu_0 

    def get_simple(self, prime: int, is_anti: bool = False, color: Optional[str] = None) -> GrothendieckObject:
        if prime not in self.generators:
            simp = SimpleObject(f"Unknown Simple ({prime})", prime, 0.0, 0.5, color, is_anti)
        else:
            base_simp = self.generators[prime]
            name = base_simp.name if prime in (0, 1) else (f"Anti-{base_simp.name}" if is_anti else base_simp.name)
            simp = SimpleObject(name, prime, base_simp.mass, base_simp.spin, color, is_anti)

        val = prime if not is_anti else -prime
        matrix = [[complex(val, 0), complex(0, 1)], [complex(0, -1), complex(-val, 0)]] if prime != 0 else [[complex(1, 0), complex(0, 0)], [complex(0, 0), complex(1, 0)]]
        mag = (Fraction(1, prime) if is_anti else prime) if prime != 0 else 0
        sig = (float(mag) * mp.exp(1j * mp.pi * simp.spin)) if mag != 0 else 0j
        return GrothendieckObject(signature=sig, mass=simp.mass, factors=[simp], extensions=[], matrix=matrix)

    def is_color_singlet(self, obj: GrothendieckObject) -> bool:
        net = {'red': 0, 'green': 0, 'blue': 0}
        for f in obj.factors:
            if f.color:
                base = f.color.split('_')[0]
                val = -1 if f.is_anti else 1
                for c in ('red', 'green', 'blue'):
                    if c in base: net[c] += val
        return (len(obj.factors) > 0) and (net['red'] == net['green'] == net['blue'])

    def exact_sequence_reconstruction(self, A: GrothendieckObject, B: GrothendieckObject, ext: Optional[ExtensionClass] = None) -> GrothendieckObject:
        for f1 in A.factors:
            for f2 in B.factors:
                if (f1.spin % 1) != 0.0:
                    if (f1.identifier == f2.identifier and
                        f1.spin == f2.spin and
                        f1.color == f2.color and
                        f1.is_anti == f2.is_anti):
                        raise PauliExclusionError(f"Pauli Exclusion Principle violation: Identical fermions {f1.name} (color={f1.color}) cannot occupy the same state.")

        sig_C = A.signature * B.signature
        mass_C = A.mass + B.mass
        ext_list = list(A.extensions) + list(B.extensions)
        matrix_C = mat_mul(A.matrix, B.matrix)

        if ext is not None:
            ext_copy = copy.deepcopy(ext)
            if not ext_copy.virtual_nodes:
                ext_copy.virtual_nodes = list(A.factors) + list(B.factors)
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
        optimal = len(A.factors) + len(B.factors)
        if self.is_color_singlet(A) and self.is_color_singlet(B):
            Z_A, N_A = get_Z_N(A)
            Z_B, N_B = get_Z_N(B)
            cond = getattr(self, 'nucleon_condensate', None)
            return geom_friction(Z_A + Z_B, N_A + N_B, cond) - (geom_friction(Z_A, N_A, cond) + geom_friction(Z_B, N_B, cond))
        else:
            len_A = 1 if self.is_color_singlet(A) else len(A.factors)
            len_B = 1 if self.is_color_singlet(B) else len(B.factors)
            virt_A = 0 if self.is_color_singlet(A) else sum(len(e.virtual_nodes) for e in A.extensions)
            virt_B = 0 if self.is_color_singlet(B) else sum(len(e.virtual_nodes) for e in B.extensions)
            return virt_A + virt_B + len_A + len_B

    def confinement_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        delta_L = self.calculate_friction(A, B)
        spin_scalar = 0.0
        if hasattr(self, 'kappa_spin'):
            parallel_scalar = sum((mp.exp(1j * mp.pi * f1.spin) * mp.exp(-1j * mp.pi * f2.spin)).real for f1 in A.factors for f2 in B.factors)
            anti_scalar = sum((mp.exp(1j * mp.pi * f1.spin) * mp.exp(1j * mp.pi * f2.spin)).real for f1 in A.factors for f2 in B.factors)
            if anti_scalar < parallel_scalar:
                spin_scalar = anti_scalar
                B.signature = B.signature.conjugate()
                for f in B.factors: f.spin = -f.spin
            else:
                spin_scalar = parallel_scalar

        def get_charge(f):
            if f.identifier == 3: return (2.0/3.0) * (-1 if f.is_anti else 1)
            if f.identifier == 5: return (-1.0/3.0) * (-1 if f.is_anti else 1)
            return 0.0

        electrostatic_scalar = sum(get_charge(f1) * get_charge(f2) for f1 in A.factors for f2 in B.factors)
        # SU(3) color-junction QED screening at color-singlet baryon closure
        singlet_screening = 0.0
        combined_factors = list(A.factors) + list(B.factors)
        dummy_obj = GrothendieckObject(signature=0j, mass=0.0, factors=combined_factors)
        if self.is_color_singlet(dummy_obj):
            singlet_screening = - CONFIG.alpha * (1.0 - 1.0 / mp.sqrt(3.0)) * self.kappa_confinement

        binding_energy = (delta_L * self.kappa_confinement) + (self.kappa_spin * spin_scalar) + (self.kappa_em * electrostatic_scalar) + singlet_screening
        ext = ExtensionClass(name, binding_energy=binding_energy, virtual_nodes=combined_factors)
        return self.exact_sequence_reconstruction(A, B, ext)


    def nuclear_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        base_friction = self.calculate_friction(A, B)
        total_friction = base_friction 
        n = 1
        current_correction = base_friction * float(CONFIG.wyler_alpha)
        while abs(current_correction) > 1e-15:
            total_friction += ((-1) ** n) * current_correction
            n += 1
            current_correction *= float(CONFIG.wyler_alpha)
        binding_energy = total_friction * float(self.kappa_residual)
        ext = ExtensionClass(name, binding_energy=binding_energy, virtual_nodes=list(A.factors) + list(B.factors))
        return self.exact_sequence_reconstruction(A, B, ext)

    def electroweak_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str, binding_energy: float = -0.0000136) -> GrothendieckObject:
        ext = ExtensionClass(name, binding_energy=binding_energy, virtual_nodes=list(A.factors) + list(B.factors))
        return self.exact_sequence_reconstruction(A, B, ext)
