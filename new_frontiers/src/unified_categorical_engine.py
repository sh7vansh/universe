import cmath
import math
import copy
from typing import List, Optional, Union
from dataclasses import dataclass, field
from fractions import Fraction

def round_complex(z: complex, decimals: int = 10) -> complex:
    return complex(round(z.real, decimals), round(z.imag, decimals))

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

class PauliExclusionError(Exception):
    pass

@dataclass
class SimpleObject:
    """
    Represents a fundamental fermion in the categorical framework.
    Maps prime numbers as unique identifiers instead of physical mass.
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
    2: SimpleObject("Electron", 2, 0.511, 0.5),
    3: SimpleObject("Up Quark", 3, 2.16, 0.5),
    5: SimpleObject("Down Quark", 5, 4.67, 0.5),
    7: SimpleObject("Strange Quark", 7, 95.0, 0.5),
    11: SimpleObject("Muon", 11, 105.0, 0.5),
    13: SimpleObject("Charm Quark", 13, 1270.0, 0.5),
    17: SimpleObject("Tau", 17, 1770.0, 0.5),
    19: SimpleObject("Bottom Quark", 19, 4180.0, 0.5),
    23: SimpleObject("Top Quark", 23, 173000.0, 0.5)
}

@dataclass
class ExtensionClass:
    """
    Represents a Yoneda extension class in the Ext1 tower.
    Logs binding energy, CP violation matrices, and virtual state memory.
    """
    name: str
    binding_energy: float 
    matrix: Optional[List[List[complex]]] = None
    virtual_nodes: List[SimpleObject] = field(default_factory=list)

@dataclass
class GrothendieckObject:
    """
    Represents a composite particle within the Grothendieck group K_0.
    Identified by a complex signature Z = Magnitude * e^(i * pi * Spin).
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
        raw_spin = cmath.phase(self.signature) / math.pi
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
    The main engine executing categorical tracking, binding, and decay.
    Uses discrete algebraic operations instead of continuous fields.
    
    Args:
        pure_math_mode (bool): If True, bypasses all physical mass scaling 
                               (GMOR/Yukawa) and outputs raw integer friction.
    """
    def __init__(self, pure_math_mode: bool = False):
        self.generators = SIMPLE_OBJECTS
        self.pure_math_mode = pure_math_mode
        
        # --- FIRST-PRINCIPLES BASE INPUTS ---
        self.m_u = 2.16       # Bare Up Quark (MeV)
        self.m_d = 4.67       # Bare Down Quark (MeV)
        self.f_pi = 92.07     # Pion Decay Constant (MeV)
        
        # --- MATHEMATICAL VACUUM DENSITY (RIEMANN / QED BRIDGE) ---
        # Derives the Chiral Condensate vacuum density purely from number theory and QED constants
        # X = 1/2 * pi * ln(2*pi) * alpha^-1 * sqrt(m_e)
        alpha_inv = 137.035999
        m_e = 0.51099895
        vacuum_density = 0.5 * math.pi * math.log(2 * math.pi) * alpha_inv * math.sqrt(m_e)
        self.chiral_condensate = -(vacuum_density)**3
        
        self.g_A = 1.2756     # Axial vector coupling (dimensionless)
        self.hbar_c = 197.3269804 # Conversion factor
        
        # 1. GMOR CONFINEMENT EQUATION
        self.m_pi = math.sqrt(- ((self.m_u + self.m_d) * self.chiral_condensate) / (self.f_pi**2))

        if not self.pure_math_mode:
            self.kappa_confinement = self.m_pi
            self.kappa_residual = None 
        else:
            self.kappa_confinement = 1.0
            self.kappa_residual = 1.0

    def get_simple(self, prime: int, is_anti: bool = False, color: Optional[str] = None) -> GrothendieckObject:
        """
        Instantiates a fundamental particle as a GrothendieckObject.
        Assigns reciprocal magnitude fractions for antimatter.
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
            sig = round_complex(cmath.rect(float(mag), math.pi * simp.spin)) if mag != 0 else 0j
            return GrothendieckObject(signature=sig, mass=simp.mass, factors=[simp], extensions=[], matrix=matrix)
        else:
            sig = round_complex(cmath.rect(float(prime), math.pi * simp.spin)) if prime != 0 else 0j
            return GrothendieckObject(signature=sig, mass=simp.mass, factors=[simp], extensions=[], matrix=matrix)

    def is_color_singlet(self, obj: GrothendieckObject) -> bool:
        """3. CATEGORICAL SU(3) ENCAPSULATION EQUATION"""
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

    def calculate_friction(self, A: GrothendieckObject, B: GrothendieckObject) -> int:
        """4. CATEGORICAL FRICTION EQUATION (Loewy Discrepancy)"""
        def get_virtual_count(obj):
            if self.is_color_singlet(obj): return 0 
            return sum(len(ext.virtual_nodes) for ext in obj.extensions)
        
        optimal = len(A.factors) + len(B.factors)
        len_new_virtual = self._get_shielded_length(A) + self._get_shielded_length(B)
        
        return (optimal + get_virtual_count(A) + get_virtual_count(B) + len_new_virtual) - optimal

    def confinement_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        """Natively binds simple objects using the GMOR-derived mass scale."""
        delta_L = self.calculate_friction(A, B)
        ext = ExtensionClass(name, binding_energy=(delta_L * self.kappa_confinement))
        ext.virtual_nodes = list(A.factors) + list(B.factors)
        return self.exact_sequence_reconstruction(A, B, ext)

    def calculate_residual_scale(self, emergent_nucleon_mass: float):
        """2. GOLDBERGER-TREIMAN & YUKAWA RESIDUAL EQUATION"""
        if self.pure_math_mode:
            self.kappa_residual = 1.0
            return
        g_pi_nn = (self.g_A * emergent_nucleon_mass) / self.f_pi
        g_sq_over_4pi = (g_pi_nn**2) / (4 * math.pi)
        r_0 = self.hbar_c / self.m_pi
        r_fm = 1.6 * r_0  
        x = r_fm / r_0
        yukawa_potential = - g_sq_over_4pi * self.m_pi * (math.exp(-x) / x)
        self.kappa_residual = yukawa_potential / 27.0 

    def nuclear_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        """Natively synthesizes nuclei with accurate negative mass defects."""
        if self.kappa_residual is None:
            raise ValueError("Must calculate residual scale from a bound nucleon first.")
        delta_L = self.calculate_friction(A, B)
        ext = ExtensionClass(name, binding_energy=(delta_L * self.kappa_residual))
        ext.virtual_nodes = list(A.factors) + list(B.factors)
        return self.exact_sequence_reconstruction(A, B, ext)

    def exact_sequence_reconstruction(self, A: GrothendieckObject, B: GrothendieckObject, ext: Optional[ExtensionClass] = None) -> GrothendieckObject:
        """
        Base Short Exact Sequence Reconstruction.
        Multiplies complex signatures (Z_C = Z_A * Z_B) and enforces Pauli Exclusion.
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
                    
                phase_shift = cmath.phase(val)
                sig_C = round_complex(sig_C * cmath.rect(1.0, phase_shift))
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

    def decoupling_algorithm(self, obj: GrothendieckObject) -> List[GrothendieckObject]:
        """
        Simulates particle decay via transfinite cellular filtration.
        Executes pure prime factorization on the signature magnitude
        to determine the constituent fundamental particles.
        """
        magnitude = abs(obj.signature)
        if magnitude < 1e-9: return [self.get_simple(0)]
        mag_frac = Fraction(round(magnitude, 10)).limit_denominator(1000000)
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
        current_mag = Fraction(round(abs(current_sig), 10)).limit_denominator(1000000)
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
            target_mag = Fraction(round(abs(target_val), 10)).limit_denominator(1000000)
            
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
    
    print("\n2. Bootstrapping Nuclear Physics (Goldberger-Treiman & Yukawa):")
    machine.calculate_residual_scale(proton.mass)
    print(f"   Dynamic Coupling (g^2/4pi): {((machine.g_A * proton.mass / machine.f_pi)**2 / (4*math.pi)):.2f}")
    
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
    electroweak_force = ExtensionClass("Electroweak Binding", -0.0000136) # -13.6 eV mass defect
    hydrogen = machine.exact_sequence_reconstruction(proton, e, electroweak_force)
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
