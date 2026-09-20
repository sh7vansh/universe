# Map: Textual TUI Modernization & Motion Overhaul

## Destination
A high-framerate, reactive three-pane terminal cockpit (`run/tui.py` backed by Textual) featuring dynamic ASCII orbital/spinor particle animations, tree navigation, and live physics telemetry, replacing the legacy curses implementation without altering underlying physics engines.

## Notes
- Framework: Textual + Rich
- Architecture: 3-pane cockpit (Left: Hierarchy Tree & Search; Center: Animated ASCII canvas; Right: Quantum/Atomic Telemetry & Inspector)
- Style: Motion-heavy, high contrast scientific HUD
- Skills: `domain-modeling`, `prototype`, `impeccable`

## Decisions so far

<!-- the index — one line per closed ticket: enough to judge relevance, then zoom the link for the detail the ticket holds -->
- [Ticket 001: Textual Dependency and Runtime Setup](tickets/001-textual-dependency-setup.md) — Configured `[project.optional-dependencies] tui` in `pyproject.toml` and installed Textual 8.2.8 / Rich 15.0.0.
- [Ticket 002: Three-Pane Cockpit Layout & Event Architecture](tickets/002-three-pane-cockpit-architecture.md) — Prototyped and verified Textual 3-pane responsive layout (Nav Tree, Motion Viewport, Telemetry Panel) with scientific HUD theme.
- [Ticket 003: High-Framerate Particle Animation Canvas](tickets/003-particle-animation-canvas.md) — Built 24 FPS `ParticleMotionCanvas` covering SU(3) color cycling, spinor precession, atomic orbital sweeps, and molecular vibrational bonds.
- [Ticket 004: Telemetry Inspector & Data Tree Integration](tickets/004-telemetry-inspector-tree.md) — Wired 185 physics entities into reactive filter tree, binding selections to dynamic Telemetry HUD and experimental error metrics.
- [Ticket 005: Parity Verification & Legacy Curses Cutover](tickets/005-legacy-cutover.md) — Completed cutover of `run/tui.py` to Textual with batch runner [B] and formula [F] modals, passing headless automated pilot tests.

## Not yet specified
- Terminal capability fallback (color profiles, Braille/Unicode vs ASCII glyph degradation)

## Out of scope
- Modifying core physics engine math (`core/quantum_engine.py`, `core/atomic_engine.py`, `core/molecular_engine.py`)
- Web/GUI frontends (GUI outside terminal)
