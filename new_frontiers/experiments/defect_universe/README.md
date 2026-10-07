# Defect as mass, travel as gravity: a discrete exploration

This is a mathematical thought experiment motivated by
[`thin-category-lattice.md`](../../../thin-category-lattice.md),
[`FunctorialGeometry.lean`](../../../math_project/MathProject/FunctorialGeometry.lean),
and the earlier [`quantum_engine.py`](../../core/quantum_engine.py).
It uses no measured particle parameters or SI units.

**Current status:** the count/defect identities and counterexamples remain
active foundations. The fixed-source interference, entanglement, and
localization demonstrations are archived references; further work focuses on
[structural mixing](../structural_mixing/README.md) and moving composites.

**Result:** a structural integer mass can be obtained by accumulating submodular
defects. Adding a local, unitary phase coupling to that mass produces interference,
source–probe entanglement, and exact localized eigenmodes around a fixed defect.
The coupling is an additional law. Neither gravitational dynamics nor a particle
mass hierarchy has been derived. The source's own formation and stability remain
open.

The [moving-object continuation](../mobile_defects/README.md) removes the fixed source
and tests whether composition can support a persistent traveling pair.

## Artifacts and reproduction

- [Exact Python experiment](run.py), using only the standard library.
- Optional HTML explorer: generate with `--with-explorer`; exports are untracked.
- [Exact results](results.json).
- [Lean algebraic proofs](../../../math_project/MathProject/DefectMassExploration.lean).

From the repository root:

```bash
python3 -m new_frontiers.experiments.defect_universe.run \
  --output-dir new_frontiers/experiments/defect_universe
cd math_project
lake env lean MathProject/DefectMassExploration.lean
```

The command above writes recorded JSON only. Add `--with-explorer` to the
Python command to recreate the optional `explorer.html` alongside it.

Python checks use exact fractions, including real and imaginary parts of all
simulated amplitudes. Decimal conversion is confined to display. The default
walk has 32 time steps; `--steps` accepts 4–64. There is no spatial truncation:
finite propagation speed makes the occupied causal cone finite at every step.
The analytic bound mode below lives on an infinite discrete line.

## 1. A valuation selected by combinatorial structure

Let the six edges of the complete graph on four vertices be the generators.
The state lattice is the Boolean lattice of its 64 edge subsets. Join and meet
are union and intersection. Define

\[
r(S)=|V|-c(V,S),\qquad M(S)=|S|-r(S),
\]

where isolated vertices count in the number of components \(c\).
This is graphic-matroid rank; \(M\) is its nullity, the number of independent
cycles. In this experiment the valuation is determined by graph connectivity,
rather than a table of mass values.

For this finite graph all 4,096 lattice pairs satisfy submodularity. Its 64
configurations have this mass distribution:

| Cycle mass | Number of configurations |
|---|---:|
| 0 | 38 |
| 1 | 19 |
| 2 | 6 |
| 3 | 1 |

A forest has mass zero. Completing a triangle produces mass one. The full
four-vertex graph has mass three. All 24 vertex relabellings preserve the mass.

This is a choice of *which* submodular rank the theory uses. Submodularity by
itself does not select graph rank, and the same Boolean lattice with cardinality
rank has zero defect everywhere.

## 2. Pair defect and intrinsic mass are related, not identical

For \(\Delta(A,B)=r(A)+r(B)-r(A\cup B)-r(A\cap B)\), cardinality inclusion–exclusion gives

\[
\boxed{\Delta(A,B)=M(A\cup B)+M(A\cap B)-M(A)-M(B).}
\]

Thus pair defect measures excess structural mass upon combination. If the
intersection is empty and the components are individually massless, their
defect equals the mass of their union. Two edges forming a path and the missing
third edge of a triangle are one example: ranks 2 and 1 combine to rank 2,
creating one unit of mass.

This generalizes to any modular size valuation \(N\) and submodular rank \(r\),
with \(M=N-r\). The identity is proved in Lean as `defect_eq_mass_excess`.
Nonnegativity of \(M\) also needs \(r\leq N\); it does not follow for arbitrary
valuations merely from this identity. Graphic rank satisfies that inequality.

For an absent edge \(e\), \(M(\{e\})=M(\varnothing)=0\), so

\[
\Delta(S,\{e\})=M(S\cup\{e\})-M(S).
\]

Summing these defects while constructing a graph gives an intrinsic mass
independent of edge order. All 1,957 edge-order histories across all subsets of
this six-edge graph were checked.

However, requiring \(m(A\vee B)=\Delta(A,B)\) for **every** decomposition forces
\(m=0\): use \(B=\bot\). This is Lean theorem `unrestricted_join_mass_zero`.
An intrinsic particle mass therefore needs admissible components, an accumulated
invariant like \(M\), or another explicit aggregation rule.

The seven minimal dependent subsets here (four triangles and three squares)
all have nullity one. This construction does not generate a hierarchy of masses
for different minimal circuits. Larger cycle mass describes multiple independent
dependencies, without yet establishing a stable particle species.

## 3. An obstruction to gravity from construction costs alone

Comparable objects have zero defect:

\[
A\leq B\Longrightarrow\Delta(A,B)=0.
\]

Therefore charging an order step by the defect of its endpoints gives no cost.
Charging it by the defect of the *added edge* gives a nonzero cost, but a second
constraint appears:

\[
S(p)=\sum_i\bigl(M(S_{i+1})-M(S_i)\bigr)
=M(S_{\mathrm{final}})-M(S_{\mathrm{initial}}).
\]

Every construction history between the same endpoints has the same action.
Mapping the additive label to a phase \(\zeta^{S(p)}\) gives the same phase to
all of them. Multiplying every term of a transition amplitude by this common
unit phase does not change its probability. Such a phase is an endpoint
potential difference, removable by rephasing the configuration basis.

This is an obstruction to this particular proposal for travel, not to every
defect-based dynamics. Lean proves the general telescoping and equal-endpoint
identities. They require no special graph assumptions once the increment form
is established.

## 4. Additional law: an existing defect affects a passing probe

The new rule couples propagation to the mass *already present*, rather than only
to mass created in a construction step.

Give each spatial site \(x\in\mathbb Z\) a graph configuration \(G_x\), hence
\(M_x=M(G_x)\). The current experiment holds these graphs fixed. Let a probe
have two direction components. Choose the exact unit phase and balanced mixer

\[
\zeta=\frac{3+4i}{5},\qquad
B=\frac12\begin{pmatrix}1+i&1-i\\1-i&1+i\end{pmatrix},
\quad |\zeta|=1,\quad B^\dagger B=I.
\]

One step is

\[
U=S B D_M,\qquad D_M|x,d\rangle=\zeta^{M_x}|x,d\rangle,
\]

where \(S|x,R\rangle=|x+1,R\rangle\) and
\(S|x,L\rangle=|x-1,L\rangle\).
Each factor is unitary, so \(U\) is unitary. A history acquires the phase

\[
\zeta^{\sum_t M_{x_t}}.
\]

Different routes can spend different numbers of steps near a defect. This
action does not telescope. The map \(k\mapsto\zeta^k\) respects addition, so
it can interpret the existing integer travel label without breaking its
concatenation law. The code's assigned label is not already tied to mass;
that tie is part of the new rule.

**Added assumptions:** the spatial adjacency, time steps, two probe directions,
complex amplitudes with the squared-norm probability rule, the mixer, the phase
\(\zeta\), and the defect–phase coupling. None is derived from thinness or
submodularity. There is no continuous-time evolution in this model. Exact
Gaussian rational amplitudes still belong to an infinite number system; a
discrete event structure need not mean a finite amplitude alphabet.

## 5. Exact interference and entanglement

In a two-arm interferometer, apply \(B\), give arm 1 phase \(\zeta^m\), and
recombine with \(B^\dagger\). The output probabilities are

\[
P_0=\frac{1+\operatorname{Re}(\zeta^m)}2,\qquad
P_1=\frac{1-\operatorname{Re}(\zeta^m)}2.
\]

| Source mass | Port 0 | Port 1 |
|---|---|---|
| 0 | 1 | 0 |
| 1 | 4/5 | 1/5 |
| 2 | 9/25 | 16/25 |
| 3 | 4/125 | 121/125 |

The phase law at mass 4 gives \(P_1=576/625\), below its mass-3 value. That
additional row in the explorer tests the phase law beyond this single graph's
maximum nullity of 3. It can represent a larger graph, but it is not another
configuration of the enumerated four-vertex graph. Response is not monotone in
mass, so a larger detector signal cannot simply be equated to stronger gravity.

If the source is in an equal-probability coherent superposition of mass zero
and mass one, the controlled gate is
\(\operatorname{diag}(1,1,1,\zeta)\). Preparing source and probe with \(B\)
gives a pure two-system state whose coefficient determinant has squared norm
\(1/20\). Its reduced purity is \(1-2/20=9/10\): genuine entanglement within
this mathematical model. Source probabilities remain \(1/2,1/2\), although its
coherences change when the probe is ignored. Source occupation is conserved by
the chosen gate, not by a derived stability mechanism.

## 6. An exact localized mode

Set \(M_0=1\) and \(M_x=0\) elsewhere. Define

\[
\lambda=\frac{9+2i}{\sqrt{85}},\quad
\rho=\frac5{\sqrt{85}},\quad
A=\frac{7+6i}{\sqrt{85}},\quad C=\sqrt{\frac3{17}}.
\]

An eigenvector of the infinite-line walk is

\[
\psi(0)=C(1,1),\qquad
\psi(x)=C(A\rho^{x-1},\rho^x)\quad(x\geq1),
\]

with \(\psi(-x)\) obtained by swapping components of \(\psi(x)\).
Write \(a=(1+i)/2\), \(b=(1-i)/2\). The boundary and bulk equations reduce to

\[
\lambda A=\zeta,\qquad
\lambda=bA+a\rho,\qquad
\lambda\rho A=aA+b\rho.
\]

Clearing square roots makes these Gaussian-rational identities, all checked
exactly by `bound_mode()` in the experiment. Reflection verifies the negative
half-line. Thus \(U\psi=\lambda\psi\), with \(|\lambda|=1\).

The probability tail ratio is \(\rho^2=5/17<1\); normalization follows from

\[
\|\psi\|^2=2C^2+2C^2\frac{1+\rho^2}{1-\rho^2}=1.
\]

In particular,

\[
P(0)=\frac6{17},\qquad
P(x)=\frac{66}{289}\left(\frac5{17}\right)^{|x|-1}\quad(x\ne0).
\]

This probability profile persists for every time step. Multiplying the mode by
\((-1)^x\) produces a second, orthogonal eigenmode with eigenvalue \(-\lambda\).
The initial probe \(|0,R\rangle\) has squared overlap \(3/17\) with each, so
its projection onto their span has norm squared \(6/17\), conserved for all time.
This statement is stronger than a finite simulation showing probability near
the origin. It does not assert that the simulation state itself is stationary.

With no defect, the same boundary ansatz gives \(|\rho|^2=1\), which does not
normalize on the infinite line. The defect-induced phase is responsible for
localization in this construction.

The source loop remains an imposed background; the probe mode is localized by
it. This is not yet a self-supporting particle made from its own dynamical
defect. The eigenphase also has not been identified with an operational inertial
rest mass.

## 7. Finite-time checks and controls

Starting from \(|0,R\rangle\), after 32 steps:

| Background | Probability within \(|x|\leq4\), rounded |
|---|---:|
| Zero mass everywhere | 0.098737 |
| One-cycle source at zero | 0.353129 |
| Two-cycle source at zero | 0.573058 |
| One unit of mass at every site | 0.098737 |

The uniform background contributes only a global phase \(\zeta^t\). Its
position probabilities agree exactly with the zero-mass control at every
tested time. Localized fields instead change relative phases. All four runs
have exact norm one at every step, and applying the exact inverse for 32 steps
recovers the initial state. All 4,096 rank comparisons and all 1,957
construction histories were exhaustively checked, not sampled.

The Python checks plus the analytic recurrence argument establish these
results for the stated model. They are separate from Lean verification:
the new Lean module proves the lattice and telescoping identities, not the
infinite-line spectral result or all quantum mechanics. Its axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry`.

## 8. Why the orders must be distinguished

There are two orders here: inclusion of graph generators and temporal
reachability of probe events. The coupling connects their data, but the
experiment has not identified them as one poset.

A finite configuration poset cannot support nontrivial unitary evolution that
only moves strictly upward or stays put. In a linear extension of the poset,
such a unitary matrix is triangular. Orthogonality and normalization of its
columns force it to be diagonal, leaving only phases. Thus a monotone
construction filtration alone is not reversible quantum dynamics.

A time-ordered event poset avoids that obstruction: configurations can change
reversibly between different time slices. Distinct histories must still be
retained before their endpoints are collapsed to one thin-category arrow.
The existing bracket and path data are natural places to retain them.

Likewise, retaining the dependent graph generators matters. Quotienting them
down to just their linear span can forget nullity; intrinsic structural mass
then needs additional data.

There is a separate obstacle to using the associahedra themselves as the mass
lattice with their ordinary face rank. Complete the nonempty face poset of
\(K_4\), the pentagon, by adjoining the empty face. Give faces rank
\(\dim(F)+1\), with empty face rank zero. For two nonadjacent vertices,
the meet is empty and the join is the whole pentagon, so

\[
\Delta(v_1,v_3)=1+1-3-0=-1.
\]

The canonical face rank is therefore not submodular. The program checks all
144 ordered face pairs and finds ten negative pairs, precisely the ordered
nonadjacent vertex pairs. Also, the nonempty face poset alone is not a lattice:
disjoint faces have no meet in it. A new valuation or a different lattice would
be required to connect particle mass directly to the \(K_n\) geometry. The
paper's subobject lattices, Tamari lattices, and associahedral face posets must
not be silently identified.

## 9. What would justify the word gravity?

The present result is defect-dependent unitary scattering and localization.
It supplies an explicit way that a structural mass can alter travel. It does
not establish attraction between moving defects, universal free fall, clock
comparison, an inverse-square regime, or a field equation.

The next experiment should make source graphs dynamical with a reversible
local update, and make source and probe affect each other under the same
principle. It should independently measure persistence, dispersion/inertia,
and response to a second defect. A common dependence on the cycle invariant
would be evidence internal to the model; it must not be guaranteed merely by
naming two independently chosen parameters the same thing.

There are two particularly sharp open questions:

1. Can stable localized defects and their propagation law arise from one
   reversible local rule, without freezing sources or inserting a separate
   trapping potential?
2. Can the mixer and defect–phase map be constrained by the categorical
   structure strongly enough to produce predictions, rather than an arbitrary
   family of quantum walks?

There is no identification of \(K_0,K_1,K_2,\ldots\) with vacuum, photon,
electron, and quarks in this experiment. Associahedra organize composition;
spin, statistics, gauge charges, and a species-dependent mass hierarchy remain
unconstructed. Those are later tests of the proposal, not outputs of this run.
