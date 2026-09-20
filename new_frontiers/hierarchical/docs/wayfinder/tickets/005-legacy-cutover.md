# Ticket 005: Parity Verification & Legacy Curses Cutover

- **Type**: `wayfinder:prototype` (HITL)
- **Status**: Closed
- **Assignee**: agent
- **Parent**: [Map: Textual TUI Modernization & Motion Overhaul](../MAP.md)
- **Blocked By**: [Ticket 003: High-Framerate Particle Animation Canvas](003-particle-animation-canvas.md), [Ticket 004: Telemetry Inspector & Data Tree](004-telemetry-inspector-tree.md)

## Question
Does the new Textual cockpit deliver full functional parity with legacy `run/tui.py` (all particles, batch runner, formula modals, keybindings) with superior UX and animations, and how should `run/tui.py` be cut over?

## Resolution
- Implemented full feature parity in `run/tui.py`:
  - 3-pane responsive cockpit layout (Tree navigation + 24 FPS motion canvas + telemetry HUD).
  - Batch element runner modal ([B]) computing Z=1..20 mass synthesis and experimental discrepancies.
  - Quantum engine formula math overlay ([F]) detailing all 8 fundamental equations from `core/quantum_engine.py`.
  - Slash (`/`) instant focus for hierarchy search.
  - Preserved curses backup in `run/tui_curses_legacy.py`.
- Automated headless pilot test (`scratch/test_cutover.py`) passed cleanly, confirming reactive tree filtering, modal screen push/dismiss, and telemetry synchronization.
