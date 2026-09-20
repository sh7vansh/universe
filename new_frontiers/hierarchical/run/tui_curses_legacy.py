#!/usr/bin/env python3
"""
Full-screen Interactive TUI for Hierarchical Multiscale Universe Simulator.
Covers:
  - Left pane: Searchable hierarchical tree (Quarks/Leptons, Atoms 1-118, Molecules).
  - Right pane: Animated diagrams, spinor representations, experimental mass errors.
  - Interactive Modals: [B] Batch runner (Z=1..N), [F] Quantum Engine Math Formulas.
"""

import curses
import time
import math
import sys
from pathlib import Path
from fractions import Fraction

# Setup workspace
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from core.quantum_engine import CategoricalMachine, SIMPLE_OBJECTS, CONFIG, universal_mass, M_PI
from core.atomic_engine import (
    get_atom_by_symbol,
    synthesize_element,
    make_nucleon,
    PERIODIC_TABLE,
    calculate_prime_composite,
)
from core.molecular_engine import molecular_bind, parse_formula, MOLECULAR_TARGETS


# --- Data Catalog Preparation ---
def build_catalog():
    items = []

    # 1. Quantum level: fundamental particles
    qm = CategoricalMachine()
    for pid, simp in sorted(SIMPLE_OBJECTS.items()):
        if pid == 0:
            continue
        category = "Boson" if simp.spin % 1 == 0 else ("Lepton" if pid in (2, 11, 17) else "Quark")
        items.append({
            "type": "quantum",
            "category": category,
            "badge": "[Q]",
            "id": pid,
            "name": simp.name,
            "sub": f"Prime {pid} | Spin {simp.spin}",
            "mass": float(simp.mass),
            "spin": simp.spin,
            "prime": pid,
        })

    # Add Nucleons as composite quantum states
    items.append({
        "type": "nucleon",
        "category": "Hadron",
        "badge": "[H]",
        "id": "proton",
        "name": "Proton",
        "sub": "uud Bound Baryon",
        "mass": 938.272,
        "true_mass": 938.272,
        "spin": 0.5,
        "is_proton": True,
    })
    items.append({
        "type": "nucleon",
        "category": "Hadron",
        "badge": "[H]",
        "id": "neutron",
        "name": "Neutron",
        "sub": "udd Bound Baryon",
        "mass": 939.565,
        "true_mass": 939.565,
        "spin": 0.5,
        "is_proton": False,
    })

    # 2. Atomic level: unique periodic elements Z=1..118
    unique_z = {}
    for sym_key, data in PERIODIC_TABLE.items():
        z = data["Z"]
        if len(sym_key) <= 2 and sym_key.isalpha():
            if z not in unique_z or ("true_u" in data and "true_u" not in unique_z[z][1]):
                unique_z[z] = (sym_key.upper(), data)

    for z in sorted(unique_z.keys()):
        sym, data = unique_z[z]
        true_u = data.get("true_u")
        true_mev = true_u * 931.4941 if true_u is not None else None
        items.append({
            "type": "atom",
            "category": "Atom",
            "badge": "[A]",
            "id": sym.lower(),
            "symbol": sym,
            "name": data["name"],
            "sub": f"Z={z} N={data['N']}",
            "Z": z,
            "N": data["N"],
            "true_mass": true_mev,
        })

    # 3. Molecular level: target molecules
    known_mol_names = {
        "H2O": "Water", "CO2": "Carbon Dioxide", "CH4": "Methane",
        "C2H6": "Ethane", "C3H8": "Propane", "H3N": "Ammonia",
        "NaCl": "Sodium Chloride", "C2H4": "Ethylene", "C2H2": "Acetylene"
    }
    for formula in sorted(MOLECULAR_TARGETS.keys()):
        disp_name = known_mol_names.get(formula, f"{formula} Molecule")
        items.append({
            "type": "molecule",
            "category": "Molecule",
            "badge": "[M]",
            "id": formula,
            "formula": formula,
            "name": f"{formula} ({disp_name})",
            "sub": f"Formula: {formula}",
        })

    return items


# Cache for evaluated results so UI is smooth
EVAL_CACHE = {}

def get_or_eval_item(item):
    key = (item["type"], item["id"])
    if key in EVAL_CACHE:
        return EVAL_CACHE[key]

    t = item["type"]
    if t == "quantum":
        qm = CategoricalMachine()
        obj = qm.get_simple(item["prime"], color="red")
        res = {
            "title": f"{item['name']} (Prime {item['prime']})",
            "mass": float(obj.mass),
            "true_mass": None,
            "spin": obj.spin,
            "matrix": obj.matrix,
            "signature": str(obj.signature),
            "factors": [f.name for f in obj.factors],
        }
    elif t == "nucleon":
        nuc = make_nucleon(item["is_proton"], "view")
        res = {
            "title": f"{item['name']} Baryon [Color Singlet]",
            "mass": float(nuc.mass),
            "true_mass": item["true_mass"],
            "spin": nuc.spin,
            "matrix": nuc.matrix,
            "signature": str(nuc.signature),
            "factors": [f"{f.name} ({f.color})" for f in nuc.factors],
        }
    elif t == "atom":
        synth = synthesize_element(item["name"], item["Z"], item["N"], quiet=True)
        atom_obj = get_atom_by_symbol(item["id"])
        res = {
            "title": f"{item['name']} [Z={item['Z']}, N={item['N']}]",
            "mass": float(synth["mass"]),
            "true_mass": item["true_mass"],
            "spin": atom_obj.spin,
            "signature": str(atom_obj.signature),
            "factors_count": len(atom_obj.factors),
            "u_quarks": sum(1 for f in atom_obj.factors if f.identifier == 3),
            "d_quarks": sum(1 for f in atom_obj.factors if f.identifier == 5),
            "electrons": sum(1 for f in atom_obj.factors if f.identifier == 2),
            "prime_composite": synth["prime_composite"],
        }
    elif t == "molecule":
        formula = item["formula"]
        comps = parse_formula(formula)
        atoms = []
        for s, c in comps:
            for idx in range(c):
                atoms.append(get_atom_by_symbol(s, tag=f"{s}_{idx+1}"))
        mol = molecular_bind(atoms, name=formula)
        iso_mass = sum(float(a.mass) for a in atoms)
        defect = float(mol.mass) - iso_mass
        res = {
            "title": f"Molecule {formula}",
            "mass": float(mol.mass),
            "isolated_mass": iso_mass,
            "defect": defect,
            "spin": mol.spin,
            "factors_count": len(mol.factors),
            "num_atoms": len(atoms),
            "signature": str(mol.signature),
        }
    else:
        res = {}

    EVAL_CACHE[key] = res
    return res


def draw_box(win, y, x, h, w, title=""):
    try:
        win.attron(curses.color_pair(1))
        win.box()
        win.attroff(curses.color_pair(1))
        if title and w > len(title) + 4:
            win.attron(curses.color_pair(3) | curses.A_BOLD)
            win.addstr(0, 2, f" {title} ")
            win.attroff(curses.color_pair(3) | curses.A_BOLD)
    except curses.error:
        pass


def draw_animated_quark(win, y, x, tick):
    # Rotating gluon color phase
    colors = [curses.color_pair(4), curses.color_pair(2), curses.color_pair(5)]
    c1 = colors[(tick // 4) % 3]
    c2 = colors[(tick // 4 + 1) % 3]
    c3 = colors[(tick // 4 + 2) % 3]

    lines = [
        ("           ● u(3)          ", c1),
        ("          ╱      ╲         ", curses.color_pair(6)),
        ("  gluon  ╱        ╲  gluon ", curses.color_pair(6)),
        ("        ╱          ╲       ", curses.color_pair(6)),
        ("    ● u(3) ─────── ● d(5)  ", c2),
        ("            gluon          ", curses.color_pair(6)),
    ]
    for idx, (txt, col) in enumerate(lines):
        try:
            win.attron(col | curses.A_BOLD)
            win.addstr(y + idx, x, txt)
            win.attroff(col | curses.A_BOLD)
        except curses.error:
            pass


def draw_animated_atom(win, y, x, Z, N, tick):
    # Orbiting electron animation
    orbit_chars = ["○", "●", "·", "⠂", "°", "*"]
    e_pos = orbit_chars[(tick // 2) % len(orbit_chars)]

    try:
        win.attron(curses.color_pair(1))
        win.addstr(y + 0, x, f"       ╭───( {e_pos} )───╮")
        win.addstr(y + 1, x, "     ╭─│───╭───────╮───│─╮")
        win.attroff(curses.color_pair(1))

        win.attron(curses.color_pair(5) | curses.A_BOLD)
        win.addstr(y + 2, x, "   ( e ) │ Nucleus │ ( e )")
        win.attroff(curses.color_pair(5) | curses.A_BOLD)

        win.attron(curses.color_pair(1))
        win.addstr(y + 3, x, "     │ │ │ ")
        win.attroff(curses.color_pair(1))

        win.attron(curses.color_pair(4) | curses.A_BOLD)
        win.addstr(f"Z:{Z:<2d}")
        win.attroff(curses.color_pair(4) | curses.A_BOLD)

        win.attron(curses.color_pair(2) | curses.A_BOLD)
        win.addstr(f"N:{N:<2d}")
        win.attroff(curses.color_pair(2) | curses.A_BOLD)

        win.attron(curses.color_pair(1))
        win.addstr(" │ │ │")
        win.addstr(y + 4, x, "     ╰─│───╰───────╯───│─╯")
        win.addstr(y + 5, x, f"       ╰───( {e_pos} )───╯")
        win.attroff(curses.color_pair(1))
    except curses.error:
        pass


def draw_animated_molecule(win, y, x, formula, num_atoms, tick):
    pulse = "═" if (tick // 3) % 2 == 0 else "─"
    comps = parse_formula(formula)
    syms = [s.upper() for s, c in comps for _ in range(c)]
    chain = f" {pulse} ".join(f"[{s}]" for s in syms[:5])
    if len(syms) > 5:
        chain += f" ... (+{len(syms)-5})"

    try:
        win.attron(curses.color_pair(3) | curses.A_BOLD)
        win.addstr(y + 0, x, f"  Lattice Orbitals:  {chain}")
        win.attroff(curses.color_pair(3) | curses.A_BOLD)

        win.attron(curses.color_pair(6))
        win.addstr(y + 2, x, f"  Topological Friction: A3 Root Lattice")
        win.addstr(y + 3, x, f"  Pairing Bonus & Chiral Condensate Exchange Active")
        win.attroff(curses.color_pair(6))
    except curses.error:
        pass


def run_batch_elements(win, start_z=1, end_z=20):
    win.clear()
    h, w = win.getmaxyx()
    draw_box(win, 0, 0, h, w, f"BATCH SYNTHESIS: Z={start_z} to Z={end_z}")

    try:
        header = f"{'Z':<4} {'Symbol':<8} {'Name':<16} {'Mass (MeV)':<16} {'True (MeV)':<16} {'Error (MeV)':<14} {'Acc %'}"
        win.attron(curses.color_pair(3) | curses.A_BOLD)
        win.addstr(2, 3, header[:w-6])
        win.attroff(curses.color_pair(3) | curses.A_BOLD)
        win.addstr(3, 3, "─" * min(w - 6, len(header)))
        win.refresh()
    except curses.error:
        pass

    unique_z = {}
    for sym_key, data in PERIODIC_TABLE.items():
        z = data["Z"]
        if len(sym_key) <= 2 and sym_key.isalpha():
            if z not in unique_z or ("true_u" in data and "true_u" not in unique_z[z][1]):
                unique_z[z] = (sym_key.upper(), data)

    row = 4
    for z in range(start_z, end_z + 1):
        if z not in unique_z or row >= h - 2:
            continue
        sym, data = unique_z[z]
        synth = synthesize_element(data["name"], data["Z"], data["N"], true_u=data.get("true_u"), quiet=True)
        true_m = data.get("true_u") * 931.4941 if data.get("true_u") else None

        err_str = f"{synth['error']:.3f}" if synth.get("error") is not None else "N/A"
        acc_str = f"{synth['accuracy']:.3f}%" if synth.get("accuracy") is not None else "N/A"
        true_str = f"{true_m:,.2f}" if true_m is not None else "N/A"

        line = f"{z:<4} {sym:<8} {data['name'][:15]:<16} {synth['mass']:<16,.2f} {true_str:<16} {err_str:<14} {acc_str}"
        try:
            col = curses.color_pair(2) if (synth.get("accuracy") and synth["accuracy"] > 99.0) else curses.color_pair(7)
            win.attron(col)
            win.addstr(row, 3, line[:w-6])
            win.attroff(col)
            row += 1
            win.refresh()
            time.sleep(0.015)
        except curses.error:
            pass

    try:
        win.attron(curses.color_pair(3) | curses.A_BOLD)
        win.addstr(h - 2, 3, " Press any key to return to main dashboard... ")
        win.attroff(curses.color_pair(3) | curses.A_BOLD)
        win.refresh()
        win.getch()
    except curses.error:
        pass


def show_formulas_modal(win):
    win.clear()
    h, w = win.getmaxyx()
    draw_box(win, 0, 0, h, w, "MATHEMATICAL STRUCTURE & FORMULAS (core/quantum_engine.py)")

    formulas = [
        ("1. Wyler's Alpha (Fine Structure)", "alpha = (9 / (16 * pi^3)) * (pi / 120)^(1/4)  ~ 1 / 137.036"),
        ("2. Universal Prime Mass Law", "M(p) = mu_0 * ((p - 1)/2 + F_gauge)"),
        ("3. Gell-Mann-Oakes-Renner Relation", "m_pi = sqrt( - (m_u + m_d) * <q_bar q> / f_pi^2 )"),
        ("4. Lattice Nuclear Contact Friction", "F(Z, N) = Rank - Boundary - Interference - Parity - SU(4) + Shells"),
        ("5. Alternating Perturbation Sum", "F_total = sum_{n=0}^inf (-alpha)^n * F_base  =  F_base / (1 + alpha)"),
        ("6. Pauli Spinor Generator Representation", "M(p) = [[ p, i ], [ -i, -p ]]  in  sl_2(C)"),
        ("7. Complex Phase Monoidal Signature", "z_C = z_A * z_B  (Spin addition through complex phase)"),
        ("8. Molecular Topological Defect", "E_bind = -(sigma * kappa_mol) - (pi_1 * kappa_mol * pi/4) + Repulsion"),
    ]

    row = 2
    for title, eq in formulas:
        if row >= h - 3:
            break
        try:
            win.attron(curses.color_pair(3) | curses.A_BOLD)
            win.addstr(row, 3, title[:w-6])
            win.attroff(curses.color_pair(3) | curses.A_BOLD)
            row += 1
            win.attron(curses.color_pair(7))
            win.addstr(row, 5, eq[:w-8])
            win.attroff(curses.color_pair(7))
            row += 2
        except curses.error:
            pass

    try:
        win.attron(curses.color_pair(3) | curses.A_BOLD)
        win.addstr(h - 2, 3, " Press any key to return to dashboard... ")
        win.attroff(curses.color_pair(3) | curses.A_BOLD)
        win.refresh()
        win.getch()
    except curses.error:
        pass


def tui_main(stdscr):
    # Initialize terminal colors
    curses.curs_set(0)
    stdscr.nodelay(True)
    stdscr.keypad(True)
    curses.start_color()
    curses.use_default_colors()

    # Color pairs
    curses.init_pair(1, curses.COLOR_CYAN, -1)     # Borders & cyan text
    curses.init_pair(2, curses.COLOR_GREEN, -1)    # Success / accuracy
    curses.init_pair(3, curses.COLOR_MAGENTA, -1)  # Headers / badges
    curses.init_pair(4, curses.COLOR_RED, -1)      # Quark / error
    curses.init_pair(5, curses.COLOR_BLUE, -1)     # Leptons / electron
    curses.init_pair(6, curses.COLOR_YELLOW, -1)   # Mass / spins
    curses.init_pair(7, curses.COLOR_WHITE, -1)    # Normal text

    catalog = build_catalog()
    filtered_items = catalog
    selected_idx = 0
    search_query = ""
    is_searching = False
    active_tab = 0  # 0: All, 1: Quantum, 2: Atoms, 3: Molecules
    tabs = ["All", "Quantum", "Atoms", "Molecules"]

    def update_filter():
        nonlocal filtered_items, selected_idx
        q = search_query.lower()
        res = []
        for it in catalog:
            # Check tab
            if active_tab == 1 and it["type"] not in ("quantum", "nucleon"):
                continue
            if active_tab == 2 and it["type"] != "atom":
                continue
            if active_tab == 3 and it["type"] != "molecule":
                continue
            # Check search query
            if q:
                match = (q in it["name"].lower() or
                         q in it.get("symbol", "").lower() or
                         q in it.get("formula", "").lower() or
                         q in it["sub"].lower())
                if not match:
                    continue
            res.append(it)
        filtered_items = res
        selected_idx = max(0, min(selected_idx, len(filtered_items) - 1))

    tick = 0

    while True:
        max_y, max_x = stdscr.getmaxyx()
        if max_y < 20 or max_x < 70:
            stdscr.clear()
            stdscr.addstr(0, 0, "Terminal too small. Please enlarge (>= 80x24).")
            stdscr.refresh()
            time.sleep(0.1)
            ch = stdscr.getch()
            if ch in (ord('q'), ord('Q')):
                break
            continue

        stdscr.erase()

        # Layout splits
        left_w = min(36, max_x // 3)
        right_w = max_x - left_w

        # --- Top Header Bar ---
        title = "⚛  H I E R A R C H I C A L   U N I V E R S E   T U I  ⚛"
        controls = "[↑/↓] Nav  [/] Search  [Tab] Category  [B] Batch Z=1..30  [F] Formulas  [Q] Quit"
        try:
            stdscr.attron(curses.color_pair(3) | curses.A_BOLD)
            stdscr.addstr(0, max(0, (max_x - len(title)) // 2), title[:max_x])
            stdscr.attroff(curses.color_pair(3) | curses.A_BOLD)

            stdscr.attron(curses.color_pair(1))
            stdscr.addstr(1, max(0, (max_x - len(controls)) // 2), controls[:max_x])
            stdscr.attroff(curses.color_pair(1))
        except curses.error:
            pass

        # --- Left Pane Window (Item List & Tabs) ---
        left_win = stdscr.derwin(max_y - 3, left_w, 2, 0)
        draw_box(left_win, 0, 0, max_y - 3, left_w, "CATALOG")

        # Tabs display
        tab_str = " ".join([f"[{t}]" if i == active_tab else f" {t} " for i, t in enumerate(tabs)])
        try:
            left_win.attron(curses.color_pair(6) | curses.A_BOLD)
            left_win.addstr(1, 2, tab_str[:left_w-4])
            left_win.attroff(curses.color_pair(6) | curses.A_BOLD)
        except curses.error:
            pass

        # Search bar
        search_prompt = f"/{search_query}" + ("█ [Esc/↵]" if is_searching else " [/]")
        try:
            left_win.attron(curses.color_pair(7) | curses.A_DIM)
            left_win.addstr(2, 2, "─" * (left_w - 4))
            left_win.addstr(3, 2, search_prompt[:left_w-4])
            left_win.addstr(4, 2, "─" * (left_w - 4))
            left_win.attroff(curses.color_pair(7) | curses.A_DIM)
        except curses.error:
            pass

        # List items
        list_h = max_y - 3 - 6
        scroll_offset = max(0, selected_idx - list_h + 1) if selected_idx >= list_h else 0

        for r in range(list_h):
            idx = scroll_offset + r
            if idx >= len(filtered_items):
                break
            it = filtered_items[idx]
            is_sel = (idx == selected_idx)

            badge = it["badge"]
            badge_col = curses.color_pair(4) if badge == "[Q]" else (curses.color_pair(1) if badge == "[A]" else curses.color_pair(3))
            row_y = 5 + r

            try:
                if is_sel:
                    left_win.attron(curses.A_REVERSE | curses.A_BOLD)
                    left_win.addstr(row_y, 2, " " * (left_w - 4))
                    left_win.addstr(row_y, 2, f"{badge} {it['name'][:left_w-9]}")
                    left_win.attroff(curses.A_REVERSE | curses.A_BOLD)
                else:
                    left_win.attron(badge_col | curses.A_BOLD)
                    left_win.addstr(row_y, 2, badge)
                    left_win.attroff(badge_col | curses.A_BOLD)

                    left_win.attron(curses.color_pair(7))
                    left_win.addstr(row_y, 6, f" {it['name'][:left_w-9]}")
                    left_win.attroff(curses.color_pair(7))
            except curses.error:
                pass

        # --- Right Pane Window (Diagram, Info, Error Comparison) ---
        right_win = stdscr.derwin(max_y - 3, right_w, 2, left_w)
        draw_box(right_win, 0, 0, max_y - 3, right_w, "INSPECTION & TOPOLOGICAL PHYSICS")

        if filtered_items:
            sel_item = filtered_items[selected_idx]
            eval_data = get_or_eval_item(sel_item)

            # Header info
            try:
                right_win.attron(curses.color_pair(3) | curses.A_BOLD)
                right_win.addstr(1, 3, eval_data.get("title", sel_item["name"])[:right_w-6])
                right_win.attroff(curses.color_pair(3) | curses.A_BOLD)

                cat_badge = f"Level: {sel_item['category']} | Spin: {eval_data.get('spin', 'N/A')} ħ"
                right_win.attron(curses.color_pair(6))
                right_win.addstr(2, 3, cat_badge[:right_w-6])
                right_win.attroff(curses.color_pair(6))
                right_win.addstr(3, 3, "─" * (right_w - 6))
            except curses.error:
                pass

            # Diagram Area
            diag_y = 4
            if sel_item["type"] in ("quantum", "nucleon"):
                draw_animated_quark(right_win, diag_y, 5, tick)
            elif sel_item["type"] == "atom":
                draw_animated_atom(right_win, diag_y, 5, sel_item["Z"], sel_item["N"], tick)
            elif sel_item["type"] == "molecule":
                draw_animated_molecule(right_win, diag_y, 5, sel_item["formula"], eval_data.get("num_atoms", 2), tick)

            # Details & Error Table
            info_y = diag_y + 8
            try:
                right_win.addstr(info_y, 3, "─" * (right_w - 6))
                right_win.attron(curses.color_pair(1) | curses.A_BOLD)
                right_win.addstr(info_y + 1, 3, "PHYSICAL OBSERVABLES & EXPERIMENTAL ACCURACY:")
                right_win.attroff(curses.color_pair(1) | curses.A_BOLD)

                calc_m = eval_data.get("mass", 0.0)
                true_m = eval_data.get("true_mass")

                right_win.attron(curses.color_pair(7))
                right_win.addstr(info_y + 3, 5, f"Theoretical Mass (Engine) : {calc_m:,.4f} MeV")

                if true_m is not None:
                    err_mev = abs(calc_m - true_m)
                    pct_err = (err_mev / true_m) * 100.0
                    acc = 100.0 - pct_err
                    right_win.addstr(info_y + 4, 5, f"Experimental Reference    : {true_m:,.4f} MeV")

                    err_col = curses.color_pair(2) if acc >= 99.0 else curses.color_pair(4)
                    right_win.attron(err_col | curses.A_BOLD)
                    right_win.addstr(info_y + 5, 5, f"Absolute Delta Error      : {err_mev:.4f} MeV  (Accuracy: {acc:.4f}%)")
                    right_win.attroff(err_col | curses.A_BOLD)
                else:
                    right_win.addstr(info_y + 4, 5, f"Experimental Reference    : Baseline Standard Model Value")

                if "defect" in eval_data:
                    right_win.attron(curses.color_pair(6))
                    right_win.addstr(info_y + 6, 5, f"Molecular Binding Defect  : {eval_data['defect']:,.6f} MeV")
                    right_win.attroff(curses.color_pair(6))
                elif "prime_composite" in eval_data:
                    p_comp = str(eval_data['prime_composite'])
                    right_win.attron(curses.color_pair(1))
                    right_win.addstr(info_y + 6, 5, f"Grothendieck Prime Index  : {p_comp[:40]}")
                    right_win.attroff(curses.color_pair(1))
                elif "matrix" in eval_data:
                    right_win.attron(curses.color_pair(1))
                    right_win.addstr(info_y + 6, 5, f"Pauli sl_2 Matrix         : {eval_data['matrix']}")
                    right_win.attroff(curses.color_pair(1))

                right_win.attroff(curses.color_pair(7))
            except curses.error:
                pass

        # --- Footer Status Bar ---
        footer = f" Items: {len(filtered_items)}/{len(catalog)} | Active Condensate Scale m_pi={float(M_PI):.2f} MeV | Press 'B' for Batch or 'F' for Formulas "
        try:
            stdscr.attron(curses.A_REVERSE | curses.color_pair(1))
            stdscr.addstr(max_y - 1, 0, footer.ljust(max_x)[:max_x])
            stdscr.attroff(curses.A_REVERSE | curses.color_pair(1))
        except curses.error:
            pass

        stdscr.refresh()
        time.sleep(0.04)
        tick += 1

        # Input handling
        try:
            ch = stdscr.getch()
        except curses.error:
            ch = -1

        if ch == -1:
            continue

        if is_searching:
            # Enter (10, 13, 343) or Esc (27) leaves search mode
            if ch in (10, 13, 27, curses.KEY_ENTER):
                is_searching = False
            elif ch in (curses.KEY_UP,):
                selected_idx = max(0, selected_idx - 1)
            elif ch in (curses.KEY_DOWN,):
                selected_idx = min(len(filtered_items) - 1, selected_idx + 1)
            elif ch in (ord('\t'),):  # Tab also exits search
                is_searching = False
                active_tab = (active_tab + 1) % len(tabs)
                update_filter()
            elif ch in (curses.KEY_BACKSPACE, 127, 8, ord('\b')):
                search_query = search_query[:-1]
                update_filter()
            elif 32 <= ch <= 126:
                search_query += chr(ch)
                update_filter()
        else:
            if ch in (ord('q'), ord('Q')):
                break
            elif ch in (ord('/'),):
                is_searching = True
            elif ch in (ord('	'),):  # Tab
                active_tab = (active_tab + 1) % len(tabs)
                update_filter()
            elif ch in (curses.KEY_UP, ord('k')):
                selected_idx = max(0, selected_idx - 1)
            elif ch in (curses.KEY_DOWN, ord('j')):
                selected_idx = min(len(filtered_items) - 1, selected_idx + 1)
            elif ch in (curses.KEY_PPAGE,):  # Page Up
                selected_idx = max(0, selected_idx - 8)
            elif ch in (curses.KEY_NPAGE,):  # Page Down
                selected_idx = min(len(filtered_items) - 1, selected_idx + 8)
            elif ch in (ord('b'), ord('B')):
                run_batch_elements(stdscr, 1, 30)
            elif ch in (ord('f'), ord('F')):
                show_formulas_modal(stdscr)


if __name__ == "__main__":
    curses.wrapper(tui_main)
