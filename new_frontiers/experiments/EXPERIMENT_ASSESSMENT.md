# Assessment of the experiments

See [the experiment index](README.md) for the current folder layout and
execution commands. Each family now keeps its report, code, and recorded
results together; shared arithmetic and graph helpers live in `_shared/`.

Date: 2026-10-07. Scope: the six substantive experiment families in this
directory, their reports, recorded results, certificates, and accompanying
Lean modules. Source notes, output files, and explorers
support those families; they are not separate scientific experiments.

My judgment: the most valuable completed results are the obstructions to
several proposed mechanisms. The strongest continuation is the structural
mixing model connected to the Dirac generator. The folder contains substantial
mathematics about specified models, but no empirical validation of a universe
model or derived observed particle spectrum.

Scores below measure importance to this project's current research question,
not probability of physical truth, originality, code quality, or amount of
work. They are ordinal judgments; a one-point difference is approximate.
9–10 means decisive for the current direction; 7–8 means an important
foundation or bridge; 5–6 means a useful narrower branch; 3–4 means a
demonstration or repair with limited explanatory gain; 1–2 means an
unsupported interpretation or little remaining scientific value.

## Cleanup applied after assessment

The user authorized the recommended cleanup. Generated Python caches and the
two HTML explorer exports were removed. Recorded JSON, source modules, exact
certificates, and Lean proofs were preserved. Explorer generation now requires
`--with-explorer`; the exports are ignored by Git.

| Branch | Current treatment |
| --- | --- |
| M-channel clock repair | Retired from the active mass program; retained as an archived calculation. |
| Fixed-source interference and entanglement | Archived demonstrations; no further extensions planned. |
| Fixed-source localized mode | Archived solved example; moving composites remain a benchmark. |
| Static Cartan attraction | Archived reference pending a specified dynamical gravity target. |
| Observed-particle assignments | No executable assignments in these experiments; historical hypotheses remain explicitly unestablished. |

The older simulators retain these branches for reproducing their recorded
results. Source files were not removed because they contain useful diagnostics
and provide imports used by later experiments.

Cleanup verification: both simulators passed their exact four-step checks with
JSON-only output and with optional HTML output. `--with-explorer` without an
output directory is rejected. All six recorded JSON files remain readable;
deleted exports and caches are absent. No Lean proof or evolution rule changed.

## Ranking the six families

| Family | Importance /10 | What earns the score | Recommended treatment |
| --- | --- | --- | --- |
| [Proposed universe](proposed_universe/README.md) | **9** for its diagnostic results | Proves the fixed scalar-phase rule cannot make structural count determine isolated inertia. Separately exposes the mismatch in the bound pair and the missing interaction at a distance. | Preserve the diagnostic results as constraints on every successor. Pause the clock repair as the main route to relativistic mass. |
| [Structural mixing](structural_mixing/README.md) | **9** | Identifies exactly which composition assumption produces linear mixing, gives a concrete repeated-gate construction, and exhibits graph-based alternatives. | Main continuation: explain the shared direction state and its coherent extensive coupling. |
| [Relativistic bridge](relativistic_bridge/README.md) | **8** | Connects an explicit walk to the Dirac generator, with spectral/inertial identities, common limiting speed, and substantial formal verification. | Keep as the reusable bridge. Investigate its structural input rather than repeatedly verifying its standard consequences. |
| [Travel-rule selection](travel_rule_selection/README.md) | **7** | Demonstrates underdetermination and proves an important obstruction to nontrivial strictly associative defect-phase decoration of join/meet. | Consolidate its constraints. Extend it only when testing a new, independently motivated selection principle. |
| [Defect universe](defect_universe/README.md) | **7** | Establishes the graph-count interpretation and defect/count identities, exposes telescoping and face-rank problems, and provides an exact walk testbed. | Preserve the algebra and counterexamples. Treat fixed-source quantum demonstrations as supporting examples. |
| [Mobile defects](mobile_defects/README.md) | **6** | Establishes a moving bound-composite sector, including exact relative bands and conserved bound projection. | Keep as a collision/binding benchmark. Recompute binding under the new mixing rule before transferring its results. |

The scores refer to the valuable parts of each report, not every section.
In particular, the proposed-universe diagnostic earns 9; its clock extension
does not. Completed results can be important to preserve while needing little
further research time.

## The judgments behind the ranking

### Proposed universe: the strongest diagnosis

Its cleanest result is general rather than a finite plot:

\[
U_M=z^M U_0\quad\Longrightarrow\quad
U_M^t=z^{Mt}U_0^t.
\]

For a fixed object and unit-modulus scalar z, all coordinate probabilities
therefore agree with the free walk. Changing M changes a global phase but
does not change its kinetic curvature. This rules out that specific isolated
mass mechanism at every time and for every preparation within the sector.
Coherent conversion between sectors would require a different analysis.

The bound pair supplies a further useful distinction: its curvature inertia
is 2√2, while its expected located structural count is 1/3. Binding is real
within the model, but it does not establish the proposed count/inertia
identity. Likewise, absence of a mediator explains why separated supports
have no interaction under this rule; it does not disprove locally mediated
gravity in a successor model.

These findings prevent building a long theory on a failed identification.
That is more useful to the present research than another attractive plot.

### Structural mixing: the best question to pursue

Count composition on a common direction factor gives C_M=C_1^M. Its actual
derivative at the identity is M times the elementary derivative. A Hermitian,
traceless, exchange-symmetric elementary generator then has the required
gσ_x form. The explicit repeated rational gate reaches pσ_z+Mσ_x without
passing a count-dependent mass into the elementary gate.

This is a useful reduction of the assumptions. It is not yet a derivation
from the original graph/category: shared-factor composition supplies the
extensivity needed for linear mass. The mathematical implication is elementary;
the research value lies in identifying a sufficient law, implementing it
exactly, and making the remaining physical question precise.

Its graph counterexamples are equally valuable. Canonical cycle count does
not uniquely select a mixing rate or internal spectrum. More available
channels need not increase the rate seen by one normalized state. The next
result must address that distinction rather than rediscover trace(I)=M.

### Relativistic bridge: an effective use of established mathematics

It answers the user's practical question: can a small connection to a known
equation let the established framework handle the downstream mathematics?
For a chosen mass-dependent mixing law, the answer is yes in the stated
free 1+1 regime. Rest energy, small-momentum inertia, and common limiting
speed follow from the Dirac generator rather than separate postulates.

Discrete-walk realizations of Dirac and convergence analysis already exist.
[Arrighi, Forets, and Nesme](https://arxiv.org/abs/1307.3524) provide such a
construction and convergence results; information-processing constructions
also have an established precedent in
[D'Ariano and Perinotti](https://arxiv.org/abs/1306.1934).
Therefore I judge this report primarily as a successful bridge for this
project, not evidence that Dirac dynamics has uniquely emerged from thinness.
These references do not automatically prove every property of our rational
variant or the newly repeated gate.

Lean establishes actual first-order derivatives, exact unitarity, spectra,
and positive-mass curvature identities. The numerical finite-time checks
and bounded-momentum convergence argument have separate scopes. A full
iterated position-space continuum theorem is not formalized. Prescribed
curved transport is researched as a target, not implemented here.

### Travel-rule selection: valuable restrictions, weaker positive choices

Two compatible phase rules produce different probabilities on the same
lattice. This directly disproves uniqueness under the tested constraints.
The associative join/meet phase obstruction is stronger and deserves a
central place among the framework's restrictions.

The positive mixer-selection examples are less explanatory: involution,
half-reflection, full neighbor symmetry, and phase orientation are supplied
requirements. Deriving their numerical operators is correct, but choosing
these requirements largely selects the desired family. Further work is
valuable only if the next requirements have a structural or physical reason
independent of the operator one hopes to recover.

### Defect universe: preserve its foundations, reduce emphasis on its demos

The intrinsic graph count M=|E|−r and the defect/count excess identity are
essential to every later report. So are the telescope obstruction and the
counterexample showing that ordinary pentagon face rank is not submodular.
These are concrete checks against silently equating different mathematical
structures.

Interference and entanglement follow after complex amplitudes, the norm
probability rule, and appropriate gates are added. They verify a working
quantum model, but do not derive quantum mechanics from the original lattice.
The localized eigenmode is stronger than finite-time concentration, yet its
source remains fixed. It does not establish a self-supported particle or
gravity. More runs of the same setup would have low marginal value.

### Mobile defects: good binding evidence, limited leverage on the mass claim

The bound-band calculation, exponential relative tails, and conserved 2/3
projection establish substantially more than a visual impression of binding.
This is the strongest explicit composite-motion example in the folder.

Contact-induced moving bound states in quantum walks already have a primary
precedent in [Ahlbrecht and collaborators](https://arxiv.org/abs/1105.1051).
The project's useful connection is how a located graph defect supplies the
contact trigger. The report does not establish capture from generic separated
inputs, constituent creation, a particle species, or distant attraction.

The latest Dirac mixing changes the microscopic coin. The old contact band's
existence and projection cannot be assumed to survive that change. This makes
the experiment a valuable benchmark for a future unified rule, rather than
current evidence that the newest rule already binds.

## Rate the individual branches separately

| Result or branch | Importance /10 | Judgment |
| --- | --- | --- |
| Fixed scalar phase cannot change isolated kinetic inertia | **9** | Essential all-time diagnostic. |
| Strictly associative defect-phase join/meet must be trivial on realized defects | **9** | Important restriction on how the original composition can carry interactions. |
| Shared-direction count composition yields linear generator | **9** | Best current mass-selection route, conditional on its explicit added law. |
| Intrinsic count and defect/count excess identity | **8** | Foundation needed to state the hypothesis coherently. |
| Equal-count graphs can have different canonical internal spectra | **8** | Useful discrimination test for any proposed count-only reduction. |
| Walk-to-Dirac generator and spectral/inertial bridge | **8** | Established mathematics can now be reused with a specified structural input. |
| Telescoping action and ordinary face-rank counterexamples | **8** | Prevent incorrect interpretations of the original structures. |
| Moving contact-bound pair and exact bound projection | **6** | Strong internal result; presently a separate interaction model. |
| Static Cartan field and attractive cross-potential | **5** | Relevant use of the existing operator, but source/minimization laws are added and the field has no dynamics. |
| Half-reflection and parity-phase selection | **4** | Correct consequences of chosen conditions; limited explanation of why those conditions hold. |
| Fixed-source localized eigenmode | **4** | Exact spectral example; source formation and self-support remain absent. |
| M-channel clock repair as the main mass mechanism | **3** | Produces the chosen curvature scaling through an imposed delay and also scales velocities by 1/M. Lower priority for a common-speed relativistic theory. |
| Interferometer and controlled-phase entanglement demonstrations | **3** | Useful sanity checks of supplied quantum gates; limited new structural content. |
| Assigning observed particle names to counts or associahedron indices | **1** | No derived species, statistics, charges, or observed hierarchy in these experiments. |

The low clock score does not mean its algebra is wrong. It means the chosen
delay supplies the desired scaling, its channels are not derived from graph
cycles, and the resulting speed scaling makes it less suitable for the
current relativistic goal. It remains a valid example of conditional
low-momentum inertia and static-response matching.

## What deserves the next research time

1. **Construct the shared direction factor and its coupling.** Use internal
   graph dynamics and a justified reduction or interaction principle. Test
   equal-count nonisomorphic graphs. Completion requires showing why their
   relevant mixing response depends only on M, or deriving explicit surviving
   dependence on other graph data.
2. **Recover an interacting composite sector under the same new rule.** Keep
   one fixed state space; specify how contact, internal states, and direction
   mixing act together. Then compute a bound spectrum and measure inertia.
   Do not transfer the old band unchanged or resize a Hilbert space when
   located count changes.
3. **Choose the gravity target before building more field demonstrations.**
   Specify dimension or additional fields, local field degrees of freedom,
   source coupling, and backreaction. Prescribed curved Dirac propagation is
   a useful intermediate test but does not close the structural-mass question
   or generate a metric source equation.

Pause repeated fixed-source plots, additional parity-phase examples,
particle-name assignments, and attempts to reinterpret the clock delay as a
common-speed relativistic mass law. Extend a settled example only when a new
rule, unresolved claim, or meaningful discriminator needs a test.

## Evidence and organization

The strongest evidence is specific: general Lean algebra where present,
symbolic/exact spectral certificates for stated models, and exact simulations
with inverse, norm, symmetry, and control checks. Their scope matters more
than the presence of Lean or a large number of plots. Numerical agreement on
a momentum grid has less general force than a proved identity. None of these
forms of internal verification replaces experimental comparison with nature.

Keep each report with its simulator, certificate, and recorded results.
Lean modules and exact certificates are important evidence infrastructure;
they are not independent physical discoveries. HTML explorers are helpful
communication artifacts, but do not strengthen a claim merely by displaying
the same data. Current priorities are recorded in the experiment index and
the individual reports.

This assessment is a report/source/result review using the verification
already completed in the session. It introduces no new evolution laws, does
not rerun the full simulation suite, and does not establish priority or
originality in the wider literature. The cited precedents are enough to
identify known mechanisms, not an exhaustive novelty search. Existing
experiments were preserved.
