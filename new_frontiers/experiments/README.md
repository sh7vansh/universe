# Research experiments

Start with [the assessment](EXPERIMENT_ASSESSMENT.md) for the judgments and
priorities. Each experiment report records its results and assumptions.
The current direction is structural mixing connected to the Dirac generator.

Each experiment has its own folder. Its `README.md` states assumptions,
results, verification scope, and reproduction commands. `run.py` contains a
simulator or exact finite checks; `certificate.py`, where present, contains
symbolic/exact certificates. Recorded evidence is in `results.json`, and
primary-source research is in `sources.md` where available.

| Experiment | Role | Code |
| --- | --- | --- |
| [Structural mixing](structural_mixing/README.md) | Active mass-selection direction | [certificate.py](structural_mixing/certificate.py) |
| [Relativistic bridge](relativistic_bridge/README.md) | Reusable Dirac connection | [certificate.py](relativistic_bridge/certificate.py) |
| [Proposed universe](proposed_universe/README.md) | Inertia diagnostics and archived field/clock branches | [run.py](proposed_universe/run.py), [certificate.py](proposed_universe/certificate.py) |
| [Travel-rule selection](travel_rule_selection/README.md) | Underdetermination and associativity constraints | [run.py](travel_rule_selection/run.py) |
| [Defect universe](defect_universe/README.md) | Count/defect foundations and archived fixed-source examples | [run.py](defect_universe/run.py) |
| [Mobile defects](mobile_defects/README.md) | Moving-composite benchmark | [run.py](mobile_defects/run.py), [certificate.py](mobile_defects/certificate.py) |

The archived branches remain beside their original results because the same
reports contain active constraints. Their code remains available for
reproduction. No whole experiment family has been discarded.

## Run from the repository root

Use Python modules so shared and sibling imports resolve consistently:

```bash
python3 -m new_frontiers.experiments.structural_mixing.certificate
python3 -m new_frontiers.experiments.relativistic_bridge.certificate
python3 -m new_frontiers.experiments.proposed_universe.run
python3 -m new_frontiers.experiments.proposed_universe.certificate
python3 -m new_frontiers.experiments.travel_rule_selection.run
python3 -m new_frontiers.experiments.defect_universe.run
python3 -m new_frontiers.experiments.mobile_defects.run
python3 -m new_frontiers.experiments.mobile_defects.certificate
```

The simulators use the standard library. The four certificates require SymPy.
For a shorter simulator check, the defect, mobile, and proposed-universe
entry points accept `--steps 4`. See each report for its default run and
complete artifact commands. These commands print results without replacing
the recorded JSON files.

To write new results, use `--output PATH` for travel selection, proposed
universe, relativistic bridge, and structural mixing. Defect and mobile
simulators use `--output-dir DIRECTORY`; they write `results.json` and create
an HTML explorer only with `--with-explorer`. Explorer exports and Python
caches are ignored by Git.

## Shared code and Lean proofs

`_shared/` contains mathematical helpers rather than independent experiments:

- [exact.py](_shared/exact.py): Gaussian rational numbers, matrix operations,
  and Gaussian integer tuple arithmetic.
- [k4_graph.py](_shared/k4_graph.py): the six-edge complete-graph example's rank,
  intrinsic cycle count, and defect.
- [coins.py](_shared/coins.py): the exact rational direction coin shared by
  the two Dirac-related certificates.

The proposed-universe checks additionally reuse the mobile-defects evolution
for their contact diagnostic. Package initializers do not run checks.

Lean modules remain in [math_project](../../math_project/MathProject):
[DefectMassExploration](../../math_project/MathProject/DefectMassExploration.lean),
[TravelRuleSelection](../../math_project/MathProject/TravelRuleSelection.lean),
[ProposedUniverse](../../math_project/MathProject/ProposedUniverse.lean),
[RelativisticBridge](../../math_project/MathProject/RelativisticBridge.lean), and
[StructuralMixing](../../math_project/MathProject/StructuralMixing.lean).
Their scientific scope is stated in the corresponding reports. From
`math_project`, build a module with `lake build MathProject.StructuralMixing`,
substituting the relevant module name.

Recorded JSON was preserved byte for byte during organization. Some historical
snapshots contain the old certificate filenames in descriptive metadata;
use the current report links and module commands to reproduce those checks.

Organization was verified by running all eight entry points and comparing all
six regenerated result snapshots. Scientific results match after accounting
for updated descriptive filenames, and the original JSON files are unchanged
byte for byte. All local report links resolve.
