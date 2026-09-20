# Ticket 004: Telemetry Inspector & Data Tree Integration

- **Type**: `wayfinder:task` (AFK)
- **Status**: Closed
- **Assignee**: agent
- **Parent**: [Map: Textual TUI Modernization & Motion Overhaul](../MAP.md)
- **Blocked By**: [Ticket 002: Three-Pane Cockpit Architecture](002-three-pane-cockpit-architecture.md)
- **Blocks**: [Ticket 005: Parity & Legacy Curses Cutover](005-legacy-cutover.md)

## Question
How do we wire `build_catalog()` data (quarks, nucleons, atoms Z=1..118, molecules) into a Textual `Tree` / reactive filter list in the left pane and bind selections to the right telemetry HUD?

## Resolution
- Integrated `build_catalog()` data (185 physics entities across Bosons, Leptons, Quarks, Hadrons, Atoms 1-118, and Molecules) into Textual `Tree` with real-time text query filtering (`#search-box`).
- Connected tree item selection (`Tree.NodeSelected`) directly to the motion canvas and `TelemetryPanel`.
- Formatted complete physics metrics inside `TelemetryPanel`:
  - Calculated mass vs experimental mass with dynamic discrepancy percentages and color badges (<1% green, <5% yellow, red).
  - Quantum spin ($S$), SU(3) factor decomposition, and tensor signatures.
- Verified end-to-end event propagation with automated headless tests.
