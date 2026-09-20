# Ticket 002: Three-Pane Cockpit Layout & Event Architecture

- **Type**: `wayfinder:prototype` (HITL)
- **Status**: Closed
- **Assignee**: agent
- **Parent**: [Map: Textual TUI Modernization & Motion Overhaul](../MAP.md)
- **Blocked By**: [Ticket 001: Textual Dependency and Runtime Setup](001-textual-dependency-setup.md)
- **Blocks**: [Ticket 003: High-Framerate Particle Animation Canvas](003-particle-animation-canvas.md), [Ticket 004: Telemetry Inspector & Data Tree](004-telemetry-inspector-tree.md)

## Question
What reactive component hierarchy and layout grid should compose the three-pane cockpit (Left: Tree/Filter, Center: Motion Canvas, Right: Telemetry Panel) to ensure responsive resizing and zero-flicker updates?

## Resolution
- Established the Three-Pane Cockpit layout using Textual's flexbox / docking container model (`Horizontal` container containing three flex `Vertical` panes):
  1. `pane-nav` (28% width): Filter search input and reactive hierarchical tree (`Tree`).
  2. `pane-viewport` (44% width): Dedicated motion HUD canvas with high-contrast background and center alignment.
  3. `pane-telemetry` (28% width): Quantum/atomic telemetry inspector.
- Validated reactive event handling and headless headless test harness with `async with app.run_test()`.
- Theme: High-contrast scientific HUD (`#0d1117` base, `#161b22` panels, `#58a6ff` highlights).
