from mpmath import mp
mp.dps = 100

import json
from pathlib import Path
from fractions import Fraction
from core.quantum_engine import CategoricalMachine, M_E, CONFIG

# Global machine instance for standalone usage
machine = CategoricalMachine()

def make_nucleon(is_proton: bool, suffix: str):
    q1 = machine.get_simple(3, color=f"red_{suffix}")
    q2 = machine.get_simple(3 if is_proton else 5, color=f"blue_{suffix}")
    q3 = machine.get_simple(5 if is_proton else 5, color=f"green_{suffix}")
    return machine.confinement_bind(machine.confinement_bind(q1, q2, "DiQ"), q3, "Nuc")

# Pre-materialized base nucleons
base_p = make_nucleon(True, "base_p")
base_n = make_nucleon(False, "base_n")

JSON_PATH = Path(__file__).resolve().parents[1] / "assets" / "periodic_table.json"
with open(JSON_PATH, "r") as f:
    PERIODIC_TABLE = json.load(f)

def get_atom_by_symbol(symbol: str, tag: str = None):
    sym_lower = symbol.lower()
    if sym_lower not in PERIODIC_TABLE:
        raise ValueError(f"Unknown element symbol: {symbol}")
    data = PERIODIC_TABLE[sym_lower]
    return synthesize_element_core(data["name"], data["Z"], data["N"], tag)

def synthesize_element_core(name: str, Z: int, N: int, tag: str = None):
    tag_prefix = tag if tag else name

    # 1. Build Nucleus
    nucleus = make_nucleon(True, f"{tag_prefix}_p0")
    for i in range(1, Z):
        nucleus = machine.nuclear_bind(nucleus, make_nucleon(True, f"{tag_prefix}_p{i}"), f"{tag_prefix}_p{i}")
    for i in range(N):
        nucleus = machine.nuclear_bind(nucleus, make_nucleon(False, f"{tag_prefix}_n{i}"), f"{tag_prefix}_n{i}")

    # 2. Bind Electrons
    atom = nucleus
    rydberg_energy = 0.5 * M_E * (CONFIG.alpha ** 2)
    total_electron_defect = -rydberg_energy * (Z ** (7.0 / 3.0))
    e_defect_per_particle = total_electron_defect / Z if Z > 0 else 0.0

    for i in range(Z):
        e = machine.get_simple(2, color=f"{tag_prefix}_shell_{i}")
        if i % 2 == 1:
            e.factors[0].spin = -0.5
            e.signature = e.signature.conjugate()
        atom = machine.electroweak_bind(atom, e, f"{tag_prefix}_e{i}", binding_energy=e_defect_per_particle)

    return atom

def calculate_prime_composite(factors):
    comp = Fraction(1, 1)
    for f in factors:
        comp = comp / f.identifier if f.is_anti else comp * f.identifier
    return comp

def synthesize_element(name: str, Z: int, N: int, true_u: float = None, quiet: bool = False):
    atom = synthesize_element_core(name, Z, N)

    parts_mass = (Z * base_p.mass) + (N * base_n.mass) + (Z * M_E)
    mass_defect = atom.mass - parts_mass
    prime_comp = calculate_prime_composite(atom.factors)

    true_mass_mev = true_u * 931.4941 if true_u is not None else None
    error_margin = abs(atom.mass - true_mass_mev) if true_mass_mev is not None else None
    error_pct = (100 * error_margin / true_mass_mev) if true_mass_mev is not None else None
    accuracy = (100 - error_pct) if error_pct is not None else None

    if not quiet:
        u_quarks = sum(1 for f in atom.factors if f.identifier == 3)
        d_quarks = sum(1 for f in atom.factors if f.identifier == 5)
        electrons = sum(1 for f in atom.factors if f.identifier == 2)
        comp_str = str(prime_comp.numerator) if prime_comp.denominator == 1 else f"{prime_comp.numerator}/{prime_comp.denominator}"
        sig_disp = f"{comp_str[:30]}...{comp_str[-25:]} ({len(comp_str)} digits)" if len(comp_str) > 60 else comp_str

        print(f"\n=========================================\n Synthesis Complete: {name}\n=========================================")
        print(f" Theoretical Mass : {atom.mass:,.3f} MeV\n Mass Defect (BE) : {mass_defect:,.3f} MeV")
        if true_mass_mev is not None:
            print(f" Accuracy         : {accuracy:.4f}% (Error: {error_margin:,.3f} MeV)")
        print(f" Particles: {len(atom.factors)} (u:{u_quarks}, d:{d_quarks}, e:{electrons})")
        print(f" Net Spin: {atom.spin}, Signature Mag: {sig_disp}\n=========================================\n")

    return {
        "name": name, "Z": Z, "N": N, "mass": atom.mass, 
        "error": error_margin, "error_pct": error_pct, "accuracy": accuracy,
        "prime_composite": prime_comp
    }
