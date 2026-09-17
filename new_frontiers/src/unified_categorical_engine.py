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
    name: str
    identifier: int # Prime number
    mass: float
    spin: float
    color: Optional[str] = None
    is_anti: bool = False

SIMPLE_OBJECTS = {
    0: SimpleObject("Void", 0, 0.0, 0.0),
    1: SimpleObject("Photon", 1, 0.0, 1.0),
    2: SimpleObject("Electron", 2, 0.511, 0.5),
    3: SimpleObject("Up Quark", 3, 2.2, 0.5),
    5: SimpleObject("Down Quark", 5, 4.7, 0.5),
    7: SimpleObject("Strange Quark", 7, 95.0, 0.5),
    11: SimpleObject("Muon", 11, 105.0, 0.5),
    13: SimpleObject("Charm Quark", 13, 1270.0, 0.5),
    17: SimpleObject("Tau", 17, 1770.0, 0.5),
    19: SimpleObject("Bottom Quark", 19, 4180.0, 0.5),
    23: SimpleObject("Top Quark", 23, 173000.0, 0.5)
}

@dataclass
class ExtensionClass:
    """Represents the Yoneda extension class in Ext^1(a, C) providing binding energy."""
    name: str
    binding_energy: float # Additive mass contribution from binding
    matrix: Optional[List[List[complex]]] = None
    virtual_nodes: List[SimpleObject] = field(default_factory=list)

@dataclass
class GrothendieckObject:
    """
    Represents an object in the abelian category.
    - signature: The unique categorical complex signature (Magnitude * e^(i * pi * Spin)).
    - mass: V: K_0 -> R additive homomorphism.
    - factors: The simple composition factors.
    - extensions: The Ext^1 classes (binding).
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
        # Phase encodes the spin: Z = Magnitude * e^(i * pi * Spin)
        # So Spin = Phase / pi
        raw_spin = cmath.phase(self.signature) / math.pi
        rounded_spin = round(raw_spin, 5)
        if abs(rounded_spin) < 1e-9:
            return 0.0
        return rounded_spin

    def __str__(self):
        comp = [f.name for f in self.factors]
        if abs(self.signature) > 1e-9:
            # format nicely to drop .0 or +0j if possible
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
    Executes the structural algorithms of the Grothendieck category.
    """
    def __init__(self):
        self.generators = SIMPLE_OBJECTS

    def get_simple(self, prime: int, is_anti: bool = False, color: Optional[str] = None) -> GrothendieckObject:
        if prime not in self.generators:
            simp = SimpleObject(f"Unknown Simple ({prime})", prime, 0.0, 0.5, color, is_anti)
        else:
            base_simp = self.generators[prime]
            name = base_simp.name if prime in (0, 1) else (f"Anti-{base_simp.name}" if is_anti else base_simp.name)
            simp = SimpleObject(name, prime, base_simp.mass, base_simp.spin, color, is_anti)
            
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
            
            return GrothendieckObject(
                signature=sig,
                mass=simp.mass,
                factors=[simp],
                extensions=[],
                matrix=matrix
            )
        else:
            sig = round_complex(cmath.rect(float(prime), math.pi * simp.spin)) if prime != 0 else 0j
            return GrothendieckObject(
                signature=sig,
                mass=simp.mass,
                factors=[simp],
                extensions=[],
                matrix=matrix
            )

    def exact_sequence_reconstruction(self, A: GrothendieckObject, B: GrothendieckObject, ext: Optional[ExtensionClass] = None) -> GrothendieckObject:
        """
        Reconstruction (Binding/Nucleosynthesis) via Short Exact Sequence:
        0 -> A -> C -> B -> 0
        
        The composition factorizes precisely via pure complex multiplication Z_C = Z_A * Z_B. 
        The additive homomorphism (Mass) sums the base masses plus the physical manifestation of the Ext^1 class.
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
                    if found:
                        break
                    
                phase_shift = cmath.phase(val)
                sig_C = round_complex(sig_C * cmath.rect(1.0, phase_shift))
                matrix_C = mat_mul(ext_copy.matrix, AB)
                
            mass_C += ext_copy.binding_energy
            ext_list.append(ext_copy)
            
        factors_C = list(A.factors) + list(B.factors)
        
        return GrothendieckObject(
            signature=sig_C,
            mass=mass_C,
            factors=factors_C,
            extensions=ext_list,
            matrix=matrix_C
        )

    def decoupling_algorithm(self, obj: GrothendieckObject) -> List[GrothendieckObject]:
        """
        The Decoupling Algorithm (Transfinite cellular filtration).
        Breaks down a composite object by extracting simple subobjects from the 
        residual quotient via pullbacks.
        
        Numerically, this executes the exact prime factorization of the categorical signature's magnitude.
        """
        magnitude = abs(obj.signature)
        
        if magnitude < 1e-9:
            return [self.get_simple(0)]
            
        # Convert magnitude to fraction accurately to avoid floating point errors
        mag_frac = Fraction(round(magnitude, 10)).limit_denominator(1000000)
        
        if mag_frac == 1:
            return [self.get_simple(1)]
        
        def factorize(n: int) -> List[int]:
            factors = []
            d = 2
            while d * d <= n:
                while (n % d) == 0:
                    factors.append(d)
                    n //= d
                d += 1
            if n > 1:
                factors.append(n)
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
        """
        Decouples specific intermediate structures (e.g. preserving a Proton during atomic decay)
        before fully factoring the remainder.
        """
        current_sig = obj.signature
        current_mag = Fraction(round(abs(current_sig), 10)).limit_denominator(1000000)
        decoupled_objects = []
        
        available_factors = list(obj.factors)
        
        def factorize(n: int) -> List[int]:
            factors = []
            d = 2
            while d * d <= n:
                while (n % d) == 0:
                    factors.append(d)
                    n //= d
                d += 1
            if n > 1:
                factors.append(n)
            return factors
            
        for target in target_signatures:
            target_val = target if isinstance(target, complex) else complex(float(target))
            target_mag = Fraction(round(abs(target_val), 10)).limit_denominator(1000000)
            
            if target_mag != 0 and current_mag.numerator % target_mag.numerator == 0 and current_mag.denominator % target_mag.denominator == 0:
                current_mag = current_mag / target_mag
                current_sig = round_complex(current_sig / target_val)
                
                target_factors = []
                num_factors = factorize(target_mag.numerator)
                den_factors = factorize(target_mag.denominator)
                
                for f in num_factors:
                    for i, af in enumerate(available_factors):
                        if af.identifier == f and not af.is_anti:
                            target_factors.append(available_factors.pop(i))
                            break
                for f in den_factors:
                    for i, af in enumerate(available_factors):
                        if af.identifier == f and af.is_anti:
                            target_factors.append(available_factors.pop(i))
                            break
                
                comp = GrothendieckObject(signature=target_val, mass=sum(f.mass for f in target_factors), factors=target_factors)
                decoupled_objects.append(comp)
                
        remaining_simple = self.decoupling_algorithm(GrothendieckObject(signature=current_sig, mass=sum(f.mass for f in available_factors), factors=available_factors))
        decoupled_objects.extend(remaining_simple)
        
        return decoupled_objects

def run_simulation():
    machine = CategoricalMachine()
    
    print("--- CATEGORICAL STANDARD MODEL SIMULATION ---")
    
    # 1. Initialization of Simple Objects
    print("\n1. Instantiating Fundamental Generators (Simple Objects):")
    u1 = machine.get_simple(3, color="red")
    u2 = machine.get_simple(3, color="blue")
    d = machine.get_simple(5, color="green")
    e = machine.get_simple(2)
    print(f"   {u1}")
    print(f"   {d}")
    print(f"   {e}")
    
    # 2. Nucleosynthesis (Reconstruction via Extensions)
    print("\n2. Nucleosynthesis (Reconstruction via Short Exact Sequences):")
    
    # Bind two Up Quarks
    strong_force_uu = ExtensionClass("Strong Force (U-U)", 10.0)
    u_u = machine.exact_sequence_reconstruction(u1, u2, strong_force_uu)
    
    # Bind the third Down Quark to form a Proton
    strong_force_uud = ExtensionClass("Strong Force (UU-D)", 929.1) # tuning to roughly 938.2 MeV total mass
    proton = machine.exact_sequence_reconstruction(u_u, d, strong_force_uud)
    print(f"   Synthesized Proton: {proton}")
    
    # Bind Electron to form Hydrogen
    electroweak_force = ExtensionClass("Electroweak Binding", -0.0000136) # -13.6 eV binding energy
    hydrogen = machine.exact_sequence_reconstruction(proton, e, electroweak_force)
    print(f"   Synthesized Hydrogen Atom: {hydrogen}")
    
    # 3. Decoupling Algorithm (Decay/Radiation)
    print("\n3. Feynman Decay (Decoupling Algorithm):")
    print(f"   Applying cellular filtration to the Hydrogen Atom (Magnitude {abs(hydrogen.signature):.3f})...")
    decoupled = machine.decoupling_algorithm(hydrogen)
    for i, obj in enumerate(decoupled):
        print(f"   Extracted Subobject {i+1}: {obj}")
        
    # 4. Weak Force & CP Violation (Virtual State Memory)
    print("\n4. Weak Force & CP Violation (Virtual State Memory):")
    charm = machine.get_simple(13, color="red")
    anti_charm = machine.get_simple(13, is_anti=True, color="red")
    
    ckm_matrix = [
        [complex(0.974, 0), complex(0.225, 0)],
        [complex(-0.225, 0), complex(0.974, 0)]
    ]
    weak_force = ExtensionClass("Weak Force (W-Boson)", 0.0, matrix=ckm_matrix)
    
    # Binding
    j_psi = machine.exact_sequence_reconstruction(charm, anti_charm, weak_force)
    print(f"   Synthesized J/Psi (Charm + Anti-Charm): {j_psi}")
    
    # Decoupling to show Virtual State memory
    decoupled_jpsi = machine.decoupling_algorithm(j_psi)
    for i, obj in enumerate(decoupled_jpsi):
        print(f"   Decoupled J/Psi Subobject {i+1}: {obj}")
        
    print(f"   Virtual State Memory logged in Extension: {[n.name for n in j_psi.extensions[0].virtual_nodes]}")

if __name__ == "__main__":
    run_simulation()
