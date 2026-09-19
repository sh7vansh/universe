from mpmath import mp
mp.dps = 100

import sys
import os
import readline
from fractions import Fraction

sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from quantum_engine import CategoricalMachine, M_E, CONFIG

# Global machine instance for standalone usage
machine = CategoricalMachine()

def make_nucleon(is_proton, suffix):
    q1 = machine.get_simple(3, color=f"red_{suffix}")
    q2 = machine.get_simple(3 if is_proton else 5, color=f"blue_{suffix}")
    q3 = machine.get_simple(5 if is_proton else 5, color=f"green_{suffix}")
    return machine.confinement_bind(machine.confinement_bind(q1, q2, "DiQ"), q3, "Nuc")

# Initialize residual scale (need a base proton)
base_p = make_nucleon(True, "base")
machine.calculate_residual_scale(base_p.mass)


import json
json_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'assets', 'periodic_table.json')
with open(json_path, 'r') as f:
    PERIODIC_TABLE = json.load(f)

def get_atom_by_symbol(symbol, tag=None):
    sym_lower = symbol.lower()
    if sym_lower not in PERIODIC_TABLE:
        raise ValueError(f"Unknown element symbol: {symbol}")
    data = PERIODIC_TABLE[sym_lower]
    return synthesize_element_core(data["name"], data["Z"], data["N"], tag)


def synthesize_element_core(name, Z, N, tag=None):
    """Core function to synthesize an element from engine."""
    tag_prefix = tag if tag else name
    
    # 1. Build Nucleus
    nucleus = make_nucleon(True, f"{tag_prefix}_p0")
    for i in range(1, Z):
        nucleus = machine.nuclear_bind(nucleus, make_nucleon(True, f"{tag_prefix}_p{i}"), f"{tag_prefix}_p{i}")
    for i in range(N):
        nucleus = machine.nuclear_bind(nucleus, make_nucleon(False, f"{tag_prefix}_n{i}"), f"{tag_prefix}_n{i}")
        
    # 2. Bind Electrons
    atom = nucleus
    
    # Calculate geometric Thomas-Fermi electron shell binding defect
    # Total atomic electron binding energy scales as Z^(7/3) * Rydberg
    rydberg_energy = 0.5 * M_E * (CONFIG.alpha ** 2)
    total_electron_defect = -rydberg_energy * (Z ** (7.0 / 3.0))
    # Distribute equally per electron for the Ext^n tower mapping
    e_defect_per_particle = total_electron_defect / Z if Z > 0 else 0.0

    for i in range(Z):
        e = machine.get_simple(2, color=f"{tag_prefix}_shell_{i}")
        if i % 2 == 1:
            e.factors[0].spin = -0.5
            e.signature = e.signature.conjugate()
        atom = machine.electroweak_bind(atom, e, f"{tag_prefix}_e{i}", binding_energy=e_defect_per_particle)
        
    return atom

def synthesize_element(name, Z, N, true_u, quiet=False):
    if not quiet:
        print(f"\n[+] Synthesizing {name} [Z={Z}, N={N}]...")
    
    atom = synthesize_element_core(name, Z, N)
    
    # Calculate masses and composition
    proton_mass = 938.346 
    neutron_mass = 939.635
    electron_mass = 0.511
    parts_mass = (Z * proton_mass) + (N * neutron_mass) + (Z * electron_mass)
    mass_defect = atom.mass - parts_mass
    
    u_quarks = sum(1 for f in atom.factors if f.identifier == 3)
    d_quarks = sum(1 for f in atom.factors if f.identifier == 5)
    electrons = sum(1 for f in atom.factors if f.identifier == 2)
    
    phase = mp.phase(atom.signature)
    
    error_margin = None
    accuracy = None
    true_mass_mev = None
    error_pct = None
    
    if true_u is not None:
        true_mass_mev = true_u * 931.4941
        error_margin = abs(atom.mass - true_mass_mev)
        error_pct = 100 * (error_margin / true_mass_mev)
        accuracy = 100 - error_pct
        
    if not quiet:
        print("\n=========================================")
        print(f" Synthesis Complete: {name}")
        print("=========================================")
        print(f" [ Mass Analysis ]")
        print(f"   Theoretical Mass : {atom.mass:,.3f} MeV")
        print(f"   Isolated Parts   : {parts_mass:,.3f} MeV")
        print(f"   Mass Defect (BE) : {mass_defect:,.3f} MeV")
        print(f"   Binding/Nucleon  : {mass_defect / (Z+N):,.3f} MeV")
        
        if true_mass_mev is not None:
            print()
            print(f" [ Accuracy & Error ]")
            print(f"   True Mass        : {true_mass_mev:,.3f} MeV")
            print(f"   Model Error      : {error_margin:,.3f} MeV")
            print(f"   Error Percentage : {error_pct:.4f}%")
            print(f"   Model Accuracy   : {accuracy:.4f}%")
            
        print()
        print(f" [ Categorical Composition ]")
        print(f"   Total Particles  : {len(atom.factors)}")
        print(f"   Up Quarks        : {u_quarks}")
        print(f"   Down Quarks      : {d_quarks}")
        print(f"   Electrons        : {electrons}")
        prime_composite = Fraction(1, 1)
        for f in atom.factors:
            if f.is_anti:
                prime_composite /= f.identifier
            else:
                prime_composite *= f.identifier
                
        print()
        print(f" [ Quantum State ]")
        print(f"   Net Spin         : {atom.spin}")
        
        if prime_composite.denominator == 1:
            comp_str = str(prime_composite.numerator)
        else:
            comp_str = f"{prime_composite.numerator}/{prime_composite.denominator}"
            
        if len(comp_str) > 60:
            print(f"   Signature Mag.   : {comp_str[:30]}...{comp_str[-25:]} ({len(comp_str)} digits)")
        else:
            print(f"   Signature Mag.   : {comp_str}")
            
        print(f"   Float Magnitude  : {abs(atom.signature):.3e}")
        print(f"   Signature Phase  : {phase:.3f} rad")
        print("=========================================\n")
        
    prime_comp = Fraction(1, 1)
    for f in atom.factors:
        if f.is_anti: prime_comp /= f.identifier
        else: prime_comp *= f.identifier

    return {
        "name": name, "Z": Z, "N": N, "mass": atom.mass, 
        "error": error_margin, "error_pct": error_pct, "accuracy": accuracy,
        "prime_composite": prime_comp
    }

def main():
    print("=========================================")
    print(" Categorical Atom Synthesizer")
    print("=========================================")
    
    # Setup autocomplete
    db_keys = list(PERIODIC_TABLE.keys()) + ["custom", "quit", "batch"]
    def completer(text, state):
        options = [k for k in db_keys if k.startswith(text.lower())]
        if state < len(options):
            match = options[state]
            return match.capitalize() if len(match) > 2 else match
        return None

    readline.parse_and_bind("tab: complete")
    readline.set_completer(completer)
    
    while True:
        print("\nType an element symbol ('Fe'), name ('Iron'), 'custom', or 'batch [start] [end]'. (Tab autocomplete, 'q' to quit)")
        query = input("> ").strip().lower()
        
        true_u = None
        if query in ('q', 'quit', 'exit'):
            break
            
        if query.startswith('batch'):
            parts = query.split()
            start_z = 1
            end_z = 118
            
            if len(parts) == 2 and parts[1].isdigit():
                end_z = int(parts[1])
            elif len(parts) == 3 and parts[1].isdigit() and parts[2].isdigit():
                start_z = int(parts[1])
                end_z = int(parts[2])
                
            print(f"\n[+] Running batch synthesis from Z={start_z} to Z={end_z}...\n")
            all_symbols = sorted([k for k in PERIODIC_TABLE.keys() if len(k) <= 2], key=lambda k: PERIODIC_TABLE[k]["Z"])
            symbols = [sym for sym in all_symbols if start_z <= PERIODIC_TABLE[sym]["Z"] <= end_z]
            
            print(f"{'Element':<15} | {'Z':<3} | {'N':<3} | {'Pred Mass (MeV)':<16} | {'Error (MeV)':<12} | {'Error %':<9} | {'Accuracy':<9} | {'Signature'}")
            print("-" * 118)
            
            total_acc = 0.0
            count = 0
            
            for sym in symbols:
                data = PERIODIC_TABLE[sym]
                res = synthesize_element(data["name"], data["Z"], data["N"], data.get("true_u"), quiet=True)
                
                prime_comp = res["prime_composite"]
                comp_str = str(prime_comp.numerator) if prime_comp.denominator == 1 else f"{prime_comp.numerator}/{prime_comp.denominator}"
                if len(comp_str) > 18:
                    sig_disp = f"{comp_str[:6]}...{comp_str[-6:]} ({len(comp_str)}d)"
                else:
                    sig_disp = comp_str

                acc_str = f"{res['accuracy']:.4f}%" if res['accuracy'] is not None else "N/A"
                err_pct_str = f"{res['error_pct']:.4f}%" if res['error_pct'] is not None else "N/A"
                err_val_str = f"{res['error']:.3f}" if res['error'] is not None else "N/A"
                accuracy_val = f"{res['accuracy']:.4f}%" if res['accuracy'] is not None else "N/A"
                print(f"{res['name']:<15} | {res['Z']:<3} | {res['N']:<3} | {res['mass']:<16,.3f} | {err_val_str:<12} | {err_pct_str:<9} | {accuracy_val:<9} | {sig_disp}")
                
                if res['accuracy'] is not None:
                    total_acc += res['accuracy']
                    count += 1
                    
            if count > 0:
                print("-" * 88)
                print(f"Average Accuracy across {count} elements: {total_acc/count:.4f}%\n")
            continue
            
        if query in PERIODIC_TABLE:
            data = PERIODIC_TABLE[query]
            synthesize_element(data["name"], data["Z"], data["N"], data.get("true_u"))
        elif query == 'custom':
            readline.set_completer(None) # disable autocomplete for custom entry
            name = input("Atom Name (e.g. Gold-197): ").strip()
            try:
                Z = int(input("Number of Protons (Z): ").strip())
                N = int(input("Number of Neutrons (N): ").strip())
            except ValueError:
                print("Please enter valid integers for Z and N.")
                readline.set_completer(completer)
                continue
            readline.set_completer(completer)
            
            if Z < 1 or N < 0:
                print("Z must be >= 1 and N >= 0.")
                continue
                
            synthesize_element(name, Z, N, None)
        else:
            matches = [k.capitalize() for k in db_keys if query in k and k not in ('custom', 'quit', 'batch')]
            if matches:
                print(f"Unknown element. Did you mean: {', '.join(matches[:5])}?")
            else:
                print(f"Unknown command '{query}'. Try 'batch', 'custom', or press Tab.")
            continue

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nExiting...")
        sys.exit(0)
