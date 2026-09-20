# Ticket 001: Textual Dependency and Runtime Setup

- **Type**: `wayfinder:task` (AFK)
- **Status**: Closed
- **Assignee**: agent
- **Parent**: [Map: Textual TUI Modernization & Motion Overhaul](../MAP.md)
- **Blocks**: [Ticket 002: Three-Pane Cockpit Architecture](002-three-pane-cockpit-architecture.md)

## Question
How should `textual` (and `rich`) be introduced into the repository dependencies (`pyproject.toml` or optional extras) and local development environment so that both headless/CI environments and terminal users have clean installation paths?

## Resolution
- Added `[project.optional-dependencies]` in `pyproject.toml` with `tui = ["textual>=0.70.0"]`, keeping core headless/math-only usage lightweight while providing a standard `pip install .[tui]` target for terminal users.
- Installed `textual` 8.2.8 and `rich` 15.0.0 in the development virtual environment.
- Verified imports in Python 3.12 environment.
