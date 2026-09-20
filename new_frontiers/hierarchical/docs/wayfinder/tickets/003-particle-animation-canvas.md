# Ticket 003: High-Framerate Particle Animation Canvas

- **Type**: `wayfinder:prototype` (HITL)
- **Status**: Closed
- **Assignee**: agent
- **Parent**: [Map: Textual TUI Modernization & Motion Overhaul](../MAP.md)
- **Blocked By**: [Ticket 002: Three-Pane Cockpit Architecture](002-three-pane-cockpit-architecture.md)
- **Blocks**: [Ticket 005: Parity & Legacy Curses Cutover](005-legacy-cutover.md)

## Question
How should the motion-heavy particle visualizer (spinors, electron orbitals, rotating molecular bonds, quantum phase cycles) be rendered at 20-30+ FPS inside a Textual custom widget without blocking UI event loop or causing frame drops?

## Resolution
- Implemented `ParticleMotionCanvas(Widget)` with a high-framerate (24 FPS) timer via `self.set_interval(1/24.0, ...)`.
- Created dynamic animated visualizers for three physical domains:
  1. Quantum/Hadron: SU(3) color charge rotation (R/G/B phase cycling), gluon exchange vectors, dynamic spinor precession vector ($S_z$, angle $\theta$), and quantum phase wave bars.
  2. Atomic: Multi-shell Bohr/orbital planetary electron sweeps, relativistic Coulomb radius metric, and nucleon center.
  3. Molecular: Covalent bond vibrational oscillations, dynamic electric dipole moment vector rotation, and stretching frequency metrics.
- Verified smooth rendering and reactive tick progression in headless test pilot.
