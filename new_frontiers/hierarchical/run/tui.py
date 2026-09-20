#!/usr/bin/env python3
"""
Interactive Multiscale Universe Cockpit TUI (Textual Modernization).
Covers:
  - Left pane: Instant Search & Categorized Hierarchy Tree (Quarks, Leptons, Hadrons, Atoms 1-118, Molecules).
  - Center pane: 24 FPS Motion Visualizer (SU(3) color cycling, spinor precession vectors, multi-shell electron clouds, vibrational molecular bonds).
  - Right pane: Quantum / Atomic Telemetry HUD with experimental true mass discrepancy metrics and tensor signatures.
  - Interactive Overlays:
      [b] Batch Element Synthesizer & Error Table (Z=1..N)
      [f] Mathematical Formulation & Quantum Engine Equations
      [?] Keybinding & Cockpit Navigation Guide
"""

import sys
import math
from pathlib import Path

# Setup workspace
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from rich.text import Text
from rich.table import Table
from textual.app import App, ComposeResult
from textual.widgets import Header, Footer, Static, Input, Tree
from textual.containers import Horizontal, Vertical
from textual.screen import ModalScreen
from textual.reactive import reactive
from textual.binding import Binding

from core.quantum_engine import CategoricalMachine, SIMPLE_OBJECTS
from core.atomic_engine import (
    get_atom_by_symbol,
    synthesize_element,
    make_nucleon,
    PERIODIC_TABLE,
)
from core.molecular_engine import parse_formula, MOLECULAR_TARGETS


# --- Data Catalog Preparation ---
def build_catalog():
    items = []

    # 1. Quantum level: fundamental particles
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

    # Nucleons
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

    # 2. Atomic elements Z=1..118
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

    # 3. Molecules
    for formula in MOLECULAR_TARGETS.keys():
        comps = parse_formula(formula)
        total_atoms = sum(c for _, c in comps)
        items.append({
            "type": "molecule",
            "category": "Molecule",
            "badge": "[M]",
            "id": formula,
            "name": f"Molecule {formula}",
            "sub": f"{len(comps)} components, {total_atoms} atoms",
            "formula": formula,
            "num_atoms": total_atoms,
        })

    return items


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
            "spin": atom_obj.spin if atom_obj else 0.0,
            "signature": str(atom_obj.signature) if atom_obj else "N/A",
            "factors_count": len(atom_obj.factors) if atom_obj else 0,
        }
    elif t == "molecule":
        comps = parse_formula(item["id"])
        total_m = 0.0
        for s, count in comps:
            at = get_atom_by_symbol(s)
            total_m += float(at.mass) * count if at else 1000.0 * count
        res = {
            "title": f"Molecular System: {item['id']}",
            "mass": total_m,
            "true_mass": None,
            "spin": "Composite J",
            "formula": item["id"],
        }
    else:
        res = {"title": item["name"], "mass": 0.0}

    EVAL_CACHE[key] = res
    return res


# --- Modals ---
class FormulasModal(ModalScreen):
    """Mathematical Formulation Overlay Modal."""
    BINDINGS = [
        Binding("escape", "dismiss", "Close"),
        Binding("q", "dismiss", "Close"),
        Binding("f", "dismiss", "Close"),
    ]

    CSS = """
    FormulasModal {
        align: center middle;
        background: rgba(10, 15, 24, 0.85);
    }
    #formula-box {
        width: 84;
        height: 85%;
        background: #111827;
        border: heavy #388bfd;
        padding: 1 2;
    }
    """

    def compose(self) -> ComposeResult:
        with Vertical(id="formula-box"):
            yield Static("[bold cyan]MATHEMATICAL STRUCTURE & FORMULAS (core/quantum_engine.py)[/]\n", classes="hud-title")

            yield Static(
                "[bold yellow]1. Wyler's Alpha (Fine Structure)[/]\n"
                "  [green]alpha = (9 / (16 * pi^3)) * (pi / 120)^(1/4)  ~ 1 / 137.036[/]\n\n"
                "[bold yellow]2. Universal Prime Mass Law[/]\n"
                "  [green]M(p) = mu_0 * ((p - 1)/2 + F_gauge)[/]\n\n"
                "[bold yellow]3. Gell-Mann-Oakes-Renner Relation[/]\n"
                "  [green]m_pi = sqrt( - (m_u + m_d) * <q_bar q> / f_pi^2 )[/]\n\n"
                "[bold yellow]4. Lattice Nuclear Contact Friction[/]\n"
                "  [green]F(Z, N) = Rank - Boundary - Interference - Parity - SU(4) + Shells[/]\n\n"
                "[bold yellow]5. Alternating Perturbation Sum[/]\n"
                "  [green]F_total = sum_{n=0}^inf (-alpha)^n * F_base  =  F_base / (1 + alpha)[/]\n\n"
                "[bold yellow]6. Pauli Spinor Generator Representation[/]\n"
                "  [green]M(p) = [[ p, i ], [ -i, -p ]]  in  sl_2(C)[/]\n\n"
                "[bold yellow]7. Complex Phase Monoidal Signature[/]\n"
                "  [green]z_C = z_A * z_B  (Spin addition through complex phase)[/]\n\n"
                "[bold yellow]8. Molecular Topological Defect[/]\n"
                "  [green]E_bind = -(sigma * kappa_mol) - (pi_1 * kappa_mol * pi/4) + Repulsion[/]\n"
            )
            yield Static("[bold #58a6ff]Press [Esc] or [F] to return to dashboard.[/]")

class BatchModal(ModalScreen):
    """Batch Element Synthesizer & Error Table."""
    BINDINGS = [
        Binding("escape", "dismiss", "Close"),
        Binding("q", "dismiss", "Close"),
        Binding("b", "dismiss", "Close"),
    ]

    CSS = """
    BatchModal {
        align: center middle;
        background: rgba(10, 15, 24, 0.88);
    }
    #batch-box {
        width: 90;
        height: 85%;
        background: #0d1117;
        border: heavy #238636;
        padding: 1 2;
    }
    """

    def compose(self) -> ComposeResult:
        with Vertical(id="batch-box"):
            yield Static("[bold green]BATCH SYNTHESIS: Z=1 to Z=20 (Periodic Table Benchmark)[/]\n")

            table = Table(box=None, expand=True)
            table.add_column("Z", style="cyan", width=4)
            table.add_column("Sym", style="bold white", width=6)
            table.add_column("Name", style="yellow", width=14)
            table.add_column("Mass (MeV)", style="green", justify="right")
            table.add_column("True (MeV)", style="blue", justify="right")
            table.add_column("Error %", justify="right")

            atoms = [itm for itm in self.app.catalog if itm.get("type") == "atom" and itm.get("Z", 0) <= 20]
            for itm in atoms:
                eval_data = get_or_eval_item(itm)
                calc_m = eval_data["mass"]
                true_m = itm.get("true_mass") or calc_m
                err = abs(calc_m - true_m) / true_m * 100 if true_m else 0.0
                color = "green" if err < 1.0 else ("yellow" if err < 5.0 else "red")
                table.add_row(
                    str(itm["Z"]), itm["symbol"], itm["name"],
                    f"{calc_m:.2f}", f"{true_m:.2f}",
                    f"[{color}]{err:.3f}%[/]"
                )

            yield Static(table)
            yield Static("\n[bold #58a6ff]Press [Esc] or [B] to return to dashboard.[/]")


# --- Dynamic Particle Motion Canvas ---
class ParticleMotionCanvas(Static):
    current_item = reactive(None)
    tick = 0

    def on_mount(self) -> None:
        self.set_interval(1 / 24.0, self.advance_frame)

    def advance_frame(self) -> None:
        self.tick += 1
        self.refresh()

    def render(self) -> Text:
        t = self.tick
        item = self.current_item
        if not item:
            return Text.from_markup("[dim]Select an entity from hierarchy to begin visualizer[/]")

        itype = item.get("type")
        angle = t * 0.12

        if itype in ("quantum", "nucleon"):
            c_colors = ["[#ff5555]● R[/]", "[#50fa7b]● G[/]", "[#8be9fd]● B[/]"]
            shift = (t // 6) % 3
            q1, q2, q3 = c_colors[shift], c_colors[(shift+1)%3], c_colors[(shift+2)%3]
            spin_x = math.cos(angle)
            spin_y = math.sin(angle)
            wave_bar = "".join(" ▂▃▄▅▆▇█"[(int(math.sin(i*0.3 + t*0.2)*3.5 + 4)) % 8] for i in range(20))

            lines = [
                f"[dim #6272a4]╔══ SU(3) GAUGE & SPINOR HUD ═══════════════╗[/]",
                f"║  Spinor Phase: [cyan]{wave_bar}[/] ║",
                f"║                                            ║",
                f"║                 {q1}                        ║",
                f"║                ╱   ╲                       ║",
                f"║         gluon ⤹     ⤸ gluon                ║",
                f"║              ╱   g   ╲                     ║",
                f"║            {q2} ═══════ {q3}                     ║",
                f"║                                            ║",
                f"║  Spin Precession: [bold #f1fa8c]{angle % (2*math.pi):.2f} rad[/]                ║",
                f"║  Phase Vector: ({spin_x:+.2f}, {spin_y:+.2f})                  ║",
                f"[dim #6272a4]╚════════════════════════════════════════════╝[/]",
            ]
            return Text.from_markup("\n".join(lines))

        elif itype == "atom":
            Z = item.get("Z", 1)
            e_chars = ["○", "●", "◈", "◇", "⠂", "✦"]
            e1 = e_chars[(t // 2) % len(e_chars)]
            e2 = e_chars[(t // 3 + 1) % len(e_chars)]
            e3 = e_chars[(t // 4 + 2) % len(e_chars)]

            lines = [
                f"[dim #6272a4]╔══ ATOMIC ELECTRON CLOUD (Z={Z:02d}) ═════════╗[/]",
                f"║                 ╭──({e1})──╮                 ║",
                f"║              ╭──│──╭───╮──│──╮              ║",
                f"║            ╭─│──│──│({e2})│──│──│─╮            ║",
                f"║           ╭│ │  │  │[bold red]●[/][bold blue]●[/]│  │  │ │╮           ║",
                f"║           ││ │  │  │[bold blue]●[/][bold red]●[/]│  │  │ ││           ║",
                f"║            ╰─│──│──│───│──│──│─╯            ║",
                f"║              ╰──│──╰───╯──│──╯              ║",
                f"║                 ╰──({e3})──╯                 ║",
                f"║                                            ║",
                f"║  Coulomb Radius: [yellow]{0.0529 * (Z**0.333):.4f} nm[/]               ║",
                f"[dim #6272a4]╚════════════════════════════════════════════╝[/]",
            ]
            return Text.from_markup("\n".join(lines))

        elif itype == "molecule":
            formula = item.get("id", "H2O")
            pulse = "═══" if (t // 4) % 2 == 0 else "───"
            dipole_ang = (t * 0.1)
            dipole = f"μ = ({math.cos(dipole_ang):+.2f}, {math.sin(dipole_ang):+.2f}) D"

            lines = [
                f"[dim #6272a4]╔══ MOLECULAR ORBITAL COUPLING ══════════════╗[/]",
                f"║  Target: [bold cyan]{formula:<12}[/] Dipole: [yellow]{dipole}[/]║",
                f"║                                            ║",
                f"║                 [bold blue][ A ][/]                        ║",
                f"║                ╱     ╲                     ║",
                f"║             {pulse}       {pulse}                  ║",
                f"║             ╱           ╲                  ║",
                f"║         [bold green][ B ][/]           [bold green][ C ][/]              ║",
                f"║                                            ║",
                f"║  Vibrational Oscillation Mode Active       ║",
                f"║  Frequency: [magenta]{1600 + 250*math.sin(t*0.2):.1f} cm⁻¹[/]                  ║",
                f"[dim #6272a4]╚════════════════════════════════════════════╝[/]",
            ]
            return Text.from_markup("\n".join(lines))

        return Text(f"Visualizer for {item.get('name', 'Unknown')}")


# --- Telemetry HUD Panel ---
class TelemetryPanel(Static):
    current_item = reactive(None)

    def watch_current_item(self, item) -> None:
        self.refresh()

    def render(self) -> Text:
        item = self.current_item
        if not item:
            return Text.from_markup("[dim]No item selected.[/]")

        eval_data = get_or_eval_item(item)
        lines = [
            f"[bold cyan]TITLE:[/] {eval_data.get('title', item.get('name'))}",
            f"[bold magenta]TYPE:[/]  {item.get('type', '').upper()} / {item.get('category', '')}",
            f"[bold green]CALCULATED MASS:[/] {eval_data.get('mass', 0.0):.6f} MeV",
        ]

        if eval_data.get("true_mass") is not None:
            tm = eval_data["true_mass"]
            m = eval_data["mass"]
            err = abs(m - tm) / tm * 100 if tm else 0.0
            lines.append(f"[bold yellow]EXPERIMENTAL:[/]    {tm:.6f} MeV")
            color = "green" if err < 1.0 else ("yellow" if err < 5.0 else "red")
            lines.append(f"[bold {color}]DISCREPANCY:[/]     {err:.3f}%")

        lines.append(f"[bold blue]SPIN (S):[/]         {eval_data.get('spin', 'N/A')}")
        if "signature" in eval_data:
            lines.append(f"[bold white]SIGNATURE:[/]        {eval_data['signature']}")

        if "factors" in eval_data:
            lines.append(f"[bold yellow]FACTORS:[/]          {', '.join(str(f) for f in eval_data['factors'][:6])}")
        elif "formula" in eval_data:
            lines.append(f"[bold yellow]FORMULA:[/]          {eval_data['formula']}")

        return Text.from_markup("\n".join(lines))


# --- Main Cockpit Application ---
class UniverseCockpitApp(App):
    """Textual Cockpit Application."""
    TITLE = "Multiscale Universe Cockpit"
    SUB_TITLE = "Quantum, Atomic & Molecular Simulator"

    BINDINGS = [
        Binding("b", "toggle_batch", "Batch Runner"),
        Binding("f", "toggle_formulas", "Math Formulas"),
        Binding("/", "focus_search", "Search Filter"),
        Binding("q", "quit", "Quit"),
    ]

    CSS = """
    Screen {
        layout: vertical;
        background: #0d1117;
        color: #c9d1d9;
    }
    #search-box {
        dock: top;
        margin: 0;
        border: solid #30363d;
    }
    #cockpit-main {
        height: 1fr;
        layout: horizontal;
    }
    #pane-nav {
        width: 28%;
        height: 100%;
        border-right: double #30363d;
        background: #0d1117;
    }
    #pane-viewport {
        width: 44%;
        height: 100%;
        border-right: double #30363d;
        background: #05080d;
        align: center middle;
    }
    #pane-telemetry {
        width: 28%;
        height: 100%;
        background: #0d1117;
        padding: 1;
    }
    .hud-title {
        color: #58a6ff;
        text-style: bold;
        background: #161b22;
        padding: 0 1;
        border-bottom: solid #30363d;
    }
    """

    def compose(self) -> ComposeResult:
        yield Header(show_clock=True)
        with Horizontal(id="cockpit-main"):
            with Vertical(id="pane-nav"):
                yield Static(" HIERARCHY SELECTOR ", classes="hud-title")
                yield Input(placeholder="[/] Filter (u, C, H2O)...", id="search-box")
                yield Tree("Universe Model", id="hierarchy-tree")

            with Vertical(id="pane-viewport"):
                yield Static(" REAL-TIME SIMULATION VIEWPORT ", classes="hud-title")
                yield ParticleMotionCanvas(id="motion-canvas")

            with Vertical(id="pane-telemetry"):
                yield Static(" QUANTUM / ATOMIC TELEMETRY ", classes="hud-title")
                yield TelemetryPanel(id="telemetry-panel")
        yield Footer()

    def on_mount(self) -> None:
        self.catalog = build_catalog()
        self.populate_tree("")

    def populate_tree(self, filter_text: str) -> None:
        tree = self.query_one("#hierarchy-tree", Tree)
        tree.clear()
        tree.root.expand()

        filt = filter_text.lower().strip()
        groups = {}
        for item in self.catalog:
            match_name = item.get("name", "").lower()
            match_id = str(item.get("id", "")).lower()
            match_sub = item.get("sub", "").lower()
            if filt and (filt not in match_name and filt not in match_id and filt not in match_sub):
                continue
            cat = item.get("category", item["type"].title())
            groups.setdefault(cat, []).append(item)

        for cat, items in groups.items():
            cat_node = tree.root.add(f"{cat} ({len(items)})", expand=True)
            for itm in items:
                badge = itm.get("badge", "[*]")
                cat_node.add_leaf(f"{badge} {itm['name']}", data=itm)

        if tree.root.children:
            first_group = tree.root.children[0]
            if first_group.children:
                self.select_item(first_group.children[0].data)

    def on_input_changed(self, event: Input.Changed) -> None:
        self.populate_tree(event.value)

    def on_tree_node_selected(self, event: Tree.NodeSelected) -> None:
        if event.node.data:
            self.select_item(event.node.data)

    def select_item(self, item) -> None:
        canvas = self.query_one("#motion-canvas", ParticleMotionCanvas)
        telemetry = self.query_one("#telemetry-panel", TelemetryPanel)
        canvas.current_item = item
        telemetry.current_item = item

    def action_focus_search(self) -> None:
        self.query_one("#search-box", Input).focus()

    def action_toggle_batch(self) -> None:
        self.push_screen(BatchModal())

    def action_toggle_formulas(self) -> None:
        self.push_screen(FormulasModal())


def main():
    app = UniverseCockpitApp()
    app.run()


if __name__ == "__main__":
    main()
