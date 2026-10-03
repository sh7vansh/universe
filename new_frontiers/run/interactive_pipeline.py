#!/usr/bin/env python3
"""
Interactive Multiscale Quantum/Atomic/Molecular Terminal Dashboard.
ANSI-styled, animated spinners, ASCII diagrams, and single/batch workflows.
"""

import sys
import time
import shutil
from pathlib import Path

# Setup workspace path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from core.quantum_engine import CategoricalMachine, SIMPLE_OBJECTS
from core.atomic_engine import get_atom_by_symbol, synthesize_element, make_nucleon, PERIODIC_TABLE
from core.molecular_engine import molecular_bind, parse_formula


# --- Styling & ANSI Palette ---
CLR_RESET   = "\033[0m"
CLR_BOLD    = "\033[1m"
CLR_DIM     = "\033[2m"
CLR_CYAN    = "\033[38;5;51m"
CLR_BLUE    = "\033[38;5;39m"
CLR_MAGENTA = "\033[38;5;201m"
CLR_YELLOW  = "\033[38;5;220m"
CLR_GREEN   = "\033[38;5;82m"
CLR_RED     = "\033[38;5;196m"
CLR_WHITE   = "\033[38;5;255m"


def spinner(msg: str, duration: float = 0.25):
    frames = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]
    start = time.time()
    idx = 0
    while time.time() - start < duration:
        print(f"\r  {CLR_CYAN}{frames[idx % len(frames)]}{CLR_RESET} {msg}", end="", flush=True)
        time.sleep(0.035)
        idx += 1
    print(f"\r  {CLR_GREEN}✔{CLR_RESET} {msg}")


def banner():
    term_w = min(shutil.get_terminal_size((80, 20)).columns, 90)
    print(f"{CLR_CYAN}{CLR_BOLD}" + "═" * term_w + f"{CLR_RESET}")
    title = "⚛  H I E R A R C H I C A L   U N I V E R S E   S I M U L A T O R  ⚛"
    subtitle = "Quarks → Hadrons → Isotopes → Molecular Orbitals"
    print(f"{CLR_MAGENTA}{CLR_BOLD}{title.center(term_w)}{CLR_RESET}")
    print(f"{CLR_DIM}{subtitle.center(term_w)}{CLR_RESET}")
    print(f"{CLR_CYAN}{CLR_BOLD}" + "═" * term_w + f"{CLR_RESET}")


def draw_quark_nucleon_diagram(p_mass: float):
    print(f"""
  {CLR_CYAN}┌──────────────────────────────────────────────┐
  │         Proton [uud] Exact Sequence          │
  └──────────────────────────────────────────────┘{CLR_RESET}
             {CLR_RED}● u{CLR_RESET} (prime 3)
            ╱     ╲
   {CLR_MAGENTA}gluon{CLR_RESET} ╱       ╲ {CLR_MAGENTA}gluon{CLR_RESET}
         ╱         ╲
    {CLR_BLUE}● u{CLR_RESET} (3) ────── {CLR_GREEN}● d{CLR_RESET} (5)
             {CLR_MAGENTA}gluon{CLR_RESET}
    Bound Mass: {CLR_YELLOW}{p_mass:,.3f} MeV{CLR_RESET}  Spin: {CLR_YELLOW}1/2 ħ{CLR_RESET}
""")


def draw_atom_diagram(sym: str, name: str, Z: int, N: int, mass: float):
    print(f"""
  {CLR_CYAN}┌──────────────────────────────────────────────┐
  │        Isotope Structure: {name:16s}   │
  └──────────────────────────────────────────────┘{CLR_RESET}
        {CLR_DIM}╭───( e⁻ )───╮{CLR_RESET}
       {CLR_DIM}│   ╭───────╮   │{CLR_RESET}
     ( e⁻ )│ {CLR_YELLOW}Nucleus{CLR_RESET} │( e⁻ )   Symbol: {CLR_BOLD}{CLR_WHITE}{sym.upper()}{CLR_RESET}  (Z={Z}, N={N})
       {CLR_DIM}│   │{CLR_RED}Z:{Z:2d}{CLR_RESET} {CLR_BLUE}N:{N:2d}{CLR_RESET}│   │{CLR_RESET}   Nucleons: {CLR_YELLOW}{Z + N}{CLR_RESET}
       {CLR_DIM}│   ╰───────╯   │{CLR_RESET}   Electrons: {CLR_CYAN}{Z}{CLR_RESET}
        {CLR_DIM}╰───( e⁻ )───╯{CLR_RESET}   Mass: {CLR_GREEN}{mass:,.3f} MeV{CLR_RESET}
""")


def draw_molecular_diagram(formula: str, atoms: list, mol_mass: float, defect: float):
    atom_str = " ─── ".join(f"{CLR_BOLD}{CLR_CYAN}[{a['sym']}]{CLR_RESET}" for a in atoms[:6])
    if len(atoms) > 6:
        atom_str += f" ... (+{len(atoms)-6} more)"
    print(f"""
  {CLR_MAGENTA}┌──────────────────────────────────────────────┐
  │     Molecular Lattice: {formula:18s}    │
  └──────────────────────────────────────────────┘{CLR_RESET}
    Orbital Chain : {atom_str}
    Bound Mass    : {CLR_GREEN}{mol_mass:,.3f} MeV{CLR_RESET}
    Defect (BE)   : {CLR_YELLOW}{defect:,.6f} MeV{CLR_RESET} (covalent + ionic + repulsion)
""")


def simulate_molecule(formula: str, show_diagrams: bool = True):
    spinner(f"Parsing topological formula: {CLR_BOLD}{formula}{CLR_RESET}", 0.15)
    parsed = parse_formula(formula)
    if not parsed:
        print(f"  {CLR_RED}Invalid formula: {formula}{CLR_RESET}")
        return None

    spinner("Synthesizing quarks and bound electron shells...", 0.25)
    atom_objects = []
    atom_info = []
    for sym, count in parsed:
        for idx in range(count):
            tag = f"{sym.upper()}_{idx+1}"
            atom = get_atom_by_symbol(sym, tag=tag)
            atom_objects.append(atom)
            atom_info.append({"sym": sym.upper(), "obj": atom})

    spinner("Re-pairing molecular orbitals & computing friction tensor...", 0.25)
    molecule = molecular_bind(atom_objects, name=formula)
    iso_mass = sum(float(a.mass) for a in atom_objects)
    bound_mass = float(molecule.mass)
    defect = bound_mass - iso_mass

    if show_diagrams:
        draw_molecular_diagram(formula, atom_info, bound_mass, defect)

    return {
        "formula": formula,
        "atoms_count": len(atom_objects),
        "factors_count": len(molecule.factors),
        "isolated_mass": iso_mass,
        "bound_mass": bound_mass,
        "defect": defect,
        "spin": molecule.spin
    }


def batch_molecular_simulation(formulas: list):
    print(f"\n{CLR_BOLD}{CLR_CYAN}=== BATCH MOLECULAR SIMULATION ({len(formulas)} items) ==={CLR_RESET}\n")
    results = []

    print(f"{CLR_BOLD}{'Formula':<10} {'Atoms':<7} {'Factors':<9} {'Iso Mass (MeV)':<16} {'Bound Mass (MeV)':<18} {'Defect (MeV)':<14} {'Spin'}{CLR_RESET}")
    print("─" * 84)

    for f in formulas:
        f = f.strip()
        if not f:
            continue
        parsed = parse_formula(f)
        if not parsed:
            continue

        atom_objects = []
        for sym, count in parsed:
            for idx in range(count):
                atom_objects.append(get_atom_by_symbol(sym, tag=f"{sym.upper()}_{idx+1}"))

        molecule = molecular_bind(atom_objects, name=f)
        iso_mass = sum(float(a.mass) for a in atom_objects)
        bound_mass = float(molecule.mass)
        defect = bound_mass - iso_mass

        res = {
            "formula": f,
            "atoms_count": len(atom_objects),
            "factors_count": len(molecule.factors),
            "isolated_mass": iso_mass,
            "bound_mass": bound_mass,
            "defect": defect,
            "spin": molecule.spin
        }
        results.append(res)
        print(f"{CLR_WHITE}{res['formula']:<10}{CLR_RESET} "
              f"{res['atoms_count']:<7} "
              f"{res['factors_count']:<9} "
              f"{res['isolated_mass']:<16,.2f} "
              f"{CLR_GREEN}{res['bound_mass']:<18,.2f}{CLR_RESET} "
              f"{CLR_YELLOW}{res['defect']:<14,.6f}{CLR_RESET} "
              f"{res['spin']}")

    print("─" * 84)
    print(f"{CLR_GREEN}Batch execution finished: {len(results)}/{len(formulas)} succeeded.{CLR_RESET}\n")
    return results


def main_menu():
    banner()
    while True:
        print(f"\n{CLR_BOLD}Select Simulation Mode:{CLR_RESET}")
        print(f"  {CLR_CYAN}1.{CLR_RESET} Interactive Molecule Synthesizer (Single Formula + Diagrams)")
        print(f"  {CLR_CYAN}2.{CLR_RESET} Batch Molecular Simulation (Pre-configured Targets or Custom List)")
        print(f"  {CLR_CYAN}3.{CLR_RESET} Layer 1 Deep Dive: Quark Confinement & Spinors")
        print(f"  {CLR_CYAN}4.{CLR_RESET} Layer 2 Deep Dive: Isotope Mass Accuracy & Periodic Table")
        print(f"  {CLR_CYAN}q.{CLR_RESET} Quit")

        choice = input(f"\n{CLR_YELLOW}Choice [1-4, q]: {CLR_RESET}").strip().lower()

        if choice == "1":
            f_in = input(f"{CLR_WHITE}Enter molecule (e.g. H2O, CH4, CO2, C2H6O, NaCl) [default: H2O]: {CLR_RESET}").strip() or "H2O"
            simulate_molecule(f_in, show_diagrams=True)

        elif choice == "2":
            print(f"\n{CLR_BOLD}Batch Sources:{CLR_RESET}")
            print("  a. Standard Target Set (H2O, CH4, CO2, C2H6, CH4O, H3N, C3H8)")
            print("  b. Enter comma-separated custom list")
            b_choice = input(f"{CLR_YELLOW}Select [a/b, default: a]: {CLR_RESET}").strip().lower() or "a"
            if b_choice == "a":
                targets = ["H2O", "CH4", "CO2", "C2H6", "CH4O", "H3N", "C3H8"]
            else:
                raw = input(f"{CLR_WHITE}Enter formulas (comma separated): {CLR_RESET}").strip()
                targets = [x.strip() for x in raw.split(",") if x.strip()]
            if targets:
                batch_molecular_simulation(targets)

        elif choice == "3":
            spinner("Initializing Category Theory Quantum Engine...", 0.25)
            qm = CategoricalMachine()
            p_demo = make_nucleon(is_proton=True, suffix="demo")
            draw_quark_nucleon_diagram(float(p_demo.mass))
            print(f"  Chiral Condensate ⟨ψ̄ψ⟩ : {CLR_CYAN}{float(qm.chiral_condensate):,.3f} MeV³{CLR_RESET}")
            print(f"  Pion Mass m_π          : {CLR_CYAN}{float(qm.m_pi):.4f} MeV{CLR_RESET}")
            print(f"  Residual Scale κ_res   : {CLR_CYAN}{float(qm.kappa_residual):.4f} MeV{CLR_RESET}")

        elif choice == "4":
            sym = input(f"{CLR_WHITE}Enter element symbol (e.g. He, C, Fe, Au) [default: Fe]: {CLR_RESET}").strip().lower() or "fe"
            if sym in PERIODIC_TABLE:
                d = PERIODIC_TABLE[sym]
                spinner(f"Synthesizing nucleus & electron shells for {d['name']}...", 0.3)
                res = synthesize_element(d["name"], d["Z"], d["N"], true_u=d.get("true_u"), quiet=True)
                draw_atom_diagram(sym, d["name"], d["Z"], d["N"], float(res["mass"]))
                if res["accuracy"]:
                    print(f"  Theoretical Accuracy: {CLR_GREEN}{res['accuracy']:.4f}%{CLR_RESET} (Error: {res['error']:.3f} MeV)")
            else:
                print(f"{CLR_RED}Unknown element: {sym}{CLR_RESET}")

        elif choice in ("q", "quit", "exit"):
            print(f"\n{CLR_CYAN}Exiting Hierarchical Simulator. Goodbye!{CLR_RESET}\n")
            break


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--batch":
        targets = sys.argv[2:] if len(sys.argv) > 2 else ["H2O", "CH4", "CO2", "C2H6", "CH4O"]
        batch_molecular_simulation(targets)
    elif len(sys.argv) > 1:
        simulate_molecule(sys.argv[1], show_diagrams=True)
    else:
        try:
            main_menu()
        except (KeyboardInterrupt, EOFError):
            print(f"\n{CLR_CYAN}Exiting.{CLR_RESET}")
