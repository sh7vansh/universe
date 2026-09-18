import sys
import os
import readline

# Ensure we can import the engine from the same directory
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from unified_categorical_engine import CategoricalMachine

def main():
    print("=========================================")
    print(" Categorical Atom Synthesizer")
    print("=========================================")
    
    machine = CategoricalMachine()
    
    def make_nucleon(is_proton, suffix):
        q1 = machine.get_simple(3, color=f"red_{suffix}")
        q2 = machine.get_simple(3 if is_proton else 5, color=f"blue_{suffix}")
        q3 = machine.get_simple(5 if is_proton else 5, color=f"green_{suffix}")
        return machine.confinement_bind(machine.confinement_bind(q1, q2, "DiQ"), q3, "Nuc")

    PERIODIC_TABLE = {
        "h": {"name": "Hydrogen-1", "Z": 1, "N": 0, "true_u": 1.007825},
        "hydrogen": {"name": "Hydrogen-1", "Z": 1, "N": 0, "true_u": 1.007825},
        "he": {"name": "Helium-4", "Z": 2, "N": 2, "true_u": 4.002603},
        "helium": {"name": "Helium-4", "Z": 2, "N": 2, "true_u": 4.002603},
        "li": {"name": "Lithium-7", "Z": 3, "N": 4, "true_u": 7.016003},
        "lithium": {"name": "Lithium-7", "Z": 3, "N": 4, "true_u": 7.016003},
        "be": {"name": "Beryllium-9", "Z": 4, "N": 5, "true_u": 9.012183},
        "beryllium": {"name": "Beryllium-9", "Z": 4, "N": 5, "true_u": 9.012183},
        "b": {"name": "Boron-11", "Z": 5, "N": 6, "true_u": 11.009305},
        "boron": {"name": "Boron-11", "Z": 5, "N": 6, "true_u": 11.009305},
        "c": {"name": "Carbon-12", "Z": 6, "N": 6, "true_u": 12.0},
        "carbon": {"name": "Carbon-12", "Z": 6, "N": 6, "true_u": 12.0},
        "n": {"name": "Nitrogen-14", "Z": 7, "N": 7, "true_u": 14.003074},
        "nitrogen": {"name": "Nitrogen-14", "Z": 7, "N": 7, "true_u": 14.003074},
        "o": {"name": "Oxygen-16", "Z": 8, "N": 8, "true_u": 15.994915},
        "oxygen": {"name": "Oxygen-16", "Z": 8, "N": 8, "true_u": 15.994915},
        "f": {"name": "Fluorine-19", "Z": 9, "N": 10, "true_u": 18.998403},
        "fluorine": {"name": "Fluorine-19", "Z": 9, "N": 10, "true_u": 18.998403},
        "ne": {"name": "Neon-20", "Z": 10, "N": 10, "true_u": 19.99244},
        "neon": {"name": "Neon-20", "Z": 10, "N": 10, "true_u": 19.99244},
        "na": {"name": "Sodium-23", "Z": 11, "N": 12, "true_u": 22.989769},
        "sodium": {"name": "Sodium-23", "Z": 11, "N": 12, "true_u": 22.989769},
        "mg": {"name": "Magnesium-24", "Z": 12, "N": 12, "true_u": 23.985042},
        "magnesium": {"name": "Magnesium-24", "Z": 12, "N": 12, "true_u": 23.985042},
        "al": {"name": "Aluminum-27", "Z": 13, "N": 14, "true_u": 26.981538},
        "aluminum": {"name": "Aluminum-27", "Z": 13, "N": 14, "true_u": 26.981538},
        "si": {"name": "Silicon-28", "Z": 14, "N": 14, "true_u": 27.976926},
        "silicon": {"name": "Silicon-28", "Z": 14, "N": 14, "true_u": 27.976926},
        "p": {"name": "Phosphorus-31", "Z": 15, "N": 16, "true_u": 30.973761},
        "phosphorus": {"name": "Phosphorus-31", "Z": 15, "N": 16, "true_u": 30.973761},
        "s": {"name": "Sulfur-32", "Z": 16, "N": 16, "true_u": 31.972071},
        "sulfur": {"name": "Sulfur-32", "Z": 16, "N": 16, "true_u": 31.972071},
        "cl": {"name": "Chlorine-35", "Z": 17, "N": 18, "true_u": 34.968852},
        "chlorine": {"name": "Chlorine-35", "Z": 17, "N": 18, "true_u": 34.968852},
        "ar": {"name": "Argon-40", "Z": 18, "N": 22, "true_u": 39.962383},
        "argon": {"name": "Argon-40", "Z": 18, "N": 22, "true_u": 39.962383},
        "k": {"name": "Potassium-39", "Z": 19, "N": 20, "true_u": 38.963706},
        "potassium": {"name": "Potassium-39", "Z": 19, "N": 20, "true_u": 38.963706},
        "ca": {"name": "Calcium-40", "Z": 20, "N": 20, "true_u": 39.96259},
        "calcium": {"name": "Calcium-40", "Z": 20, "N": 20, "true_u": 39.96259},
        "sc": {"name": "Scandium-45", "Z": 21, "N": 24, "true_u": 44.955912},
        "scandium": {"name": "Scandium-45", "Z": 21, "N": 24, "true_u": 44.955912},
        "ti": {"name": "Titanium-48", "Z": 22, "N": 26, "true_u": 47.947946},
        "titanium": {"name": "Titanium-48", "Z": 22, "N": 26, "true_u": 47.947946},
        "v": {"name": "Vanadium-51", "Z": 23, "N": 28, "true_u": 50.943959},
        "vanadium": {"name": "Vanadium-51", "Z": 23, "N": 28, "true_u": 50.943959},
        "cr": {"name": "Chromium-52", "Z": 24, "N": 28, "true_u": 51.940507},
        "chromium": {"name": "Chromium-52", "Z": 24, "N": 28, "true_u": 51.940507},
        "mn": {"name": "Manganese-55", "Z": 25, "N": 30, "true_u": 54.938045},
        "manganese": {"name": "Manganese-55", "Z": 25, "N": 30, "true_u": 54.938045},
        "fe": {"name": "Iron-56", "Z": 26, "N": 30, "true_u": 55.934937},
        "iron": {"name": "Iron-56", "Z": 26, "N": 30, "true_u": 55.934937},
        "co": {"name": "Cobalt-59", "Z": 27, "N": 32, "true_u": 58.933195},
        "cobalt": {"name": "Cobalt-59", "Z": 27, "N": 32, "true_u": 58.933195},
        "ni": {"name": "Nickel-58", "Z": 28, "N": 30, "true_u": 57.935342},
        "nickel": {"name": "Nickel-58", "Z": 28, "N": 30, "true_u": 57.935342},
        "cu": {"name": "Copper-63", "Z": 29, "N": 34, "true_u": 62.929597},
        "copper": {"name": "Copper-63", "Z": 29, "N": 34, "true_u": 62.929597},
        "zn": {"name": "Zinc-64", "Z": 30, "N": 34, "true_u": 63.929142},
        "zinc": {"name": "Zinc-64", "Z": 30, "N": 34, "true_u": 63.929142}
    }
    
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

    print("Bootstrapping nuclear residual scale...")
    base_p = make_nucleon(True, "base")
    machine.calculate_residual_scale(base_p.mass)

    def synthesize_element(name, Z, N, true_u, quiet=False):
        if not quiet:
            print(f"\n[+] Synthesizing {name} [Z={Z}, N={N}]...")
        
        # 1. Build Nucleus
        nucleus = make_nucleon(True, f"{name}_p0")
        for i in range(1, Z):
            nucleus = machine.nuclear_bind(nucleus, make_nucleon(True, f"{name}_p{i}"), f"{name}_p{i}")
        for i in range(N):
            nucleus = machine.nuclear_bind(nucleus, make_nucleon(False, f"{name}_n{i}"), f"{name}_n{i}")
            
        # 2. Bind Electrons
        atom = nucleus
        for i in range(Z):
            e = machine.get_simple(2, color=f"shell_{i}")
            if i % 2 == 1:
                e.factors[0].spin = -0.5
                e.signature = e.signature.conjugate()
            atom = machine.electroweak_bind(atom, e, f"{name}_e{i}", binding_energy=0.0)
            
        # Calculate masses and composition
        proton_mass = 938.346 
        neutron_mass = 939.635
        electron_mass = 0.511
        parts_mass = (Z * proton_mass) + (N * neutron_mass) + (Z * electron_mass)
        mass_defect = atom.mass - parts_mass
        
        u_quarks = sum(1 for f in atom.factors if f.identifier == 3)
        d_quarks = sum(1 for f in atom.factors if f.identifier == 5)
        electrons = sum(1 for f in atom.factors if f.identifier == 2)
        
        import cmath
        phase = cmath.phase(atom.signature)
        
        error_margin = None
        accuracy = None
        true_mass_mev = None
        
        if true_u is not None:
            true_mass_mev = true_u * 931.4941
            error_margin = abs(atom.mass - true_mass_mev)
            accuracy = 100 * (1 - error_margin / true_mass_mev)
            
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
                print(f"   Model Accuracy   : {accuracy:.4f}%")
                
            print()
            print(f" [ Categorical Composition ]")
            print(f"   Total Particles  : {len(atom.factors)}")
            print(f"   Up Quarks        : {u_quarks}")
            print(f"   Down Quarks      : {d_quarks}")
            print(f"   Electrons        : {electrons}")
            print()
            print(f" [ Quantum State ]")
            print(f"   Net Spin         : {atom.spin}")
            print(f"   Signature Mag.   : {abs(atom.signature):.3e}")
            print(f"   Signature Phase  : {phase:.3f} rad")
            print("=========================================\n")
            
        return {
            "name": name, "Z": Z, "N": N, "mass": atom.mass, 
            "error": error_margin, "accuracy": accuracy
        }

    while True:
        print("\nType an element symbol (e.g. 'Fe'), name ('Iron'), 'custom', or 'batch'. (Tab to autocomplete, 'q' to quit)")
        query = input("> ").strip().lower()
        
        true_u = None
        if query in ('q', 'quit', 'exit'):
            break
            
        if query == 'batch':
            print("\n[+] Running batch synthesis over entire periodic database...\n")
            symbols = sorted([k for k in PERIODIC_TABLE.keys() if len(k) <= 2], key=lambda k: PERIODIC_TABLE[k]["Z"])
            
            print(f"{'Element':<15} | {'Z':<3} | {'N':<3} | {'Pred Mass (MeV)':<16} | {'Error (MeV)':<12} | {'Accuracy'}")
            print("-" * 75)
            
            total_acc = 0.0
            count = 0
            for sym in symbols:
                data = PERIODIC_TABLE[sym]
                res = synthesize_element(data["name"], data["Z"], data["N"], data.get("true_u"), quiet=True)
                
                acc_str = f"{res['accuracy']:.4f}%" if res['accuracy'] else "N/A"
                err_str = f"{res['error']:.3f}" if res['error'] else "N/A"
                print(f"{res['name']:<15} | {res['Z']:<3} | {res['N']:<3} | {res['mass']:<16,.3f} | {err_str:<12} | {acc_str}")
                
                if res['accuracy']:
                    total_acc += res['accuracy']
                    count += 1
                    
            if count > 0:
                print("-" * 75)
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
