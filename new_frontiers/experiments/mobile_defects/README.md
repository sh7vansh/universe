# Two moving objects: can composition produce a persistent pair?

This continues the [first defect experiment](../defect_universe/README.md).
The first experiment kept a source fixed. This experiment lets both objects
move. The interaction is computed from the rank of their combined structure.

**Result:** two individually massless graph components can have a nonzero
defect when they meet. A reversible rule based on that defect supports moving
bound-pair states. No fixed source is needed. Quantum evolution and the phase
rule remain added assumptions. Gravity has not been derived.

## Read or run the experiment

- Optional HTML explorer: generate with `--with-explorer`; exports are untracked.
- [Exact simulator](run.py), standard library only.
- [Exact simulation results](results.json).
- [Symbolic bound-band certificate](certificate.py), using SymPy.

From the repository root:

```bash
python3 -m new_frontiers.experiments.mobile_defects.run \
  --output-dir new_frontiers/experiments/mobile_defects
python3 -m new_frontiers.experiments.mobile_defects.certificate
```

The simulator writes recorded JSON only by default. Add `--with-explorer` to
recreate the optional `explorer.html` in the output directory.

The simulator uses integer numerators for the real and imaginary parts of
amplitudes. After t forward steps, the common amplitude denominator is
sqrt(2) times 2^t. Thus every probability is an exact fraction. Decimal values
are used only for display. The simulator has no fitted physical constants.
The symbolic certificate was checked with SymPy 1.14.0; it is not a Lean proof.

## 1. What the objects are

Object A contains the edges (0,1) and (1,2). Object B contains edge (0,2).
Each object is an open graph with cycle count zero. They are distinguishable
components, not identified with electrons, photons, or any other species.

Place A at site x and B at site y on a discrete line. A graph vertex is the
pair (site, vertex label). The objects therefore use different graph vertices
when they are at different sites.

The rank is still graphic rank: number of vertices minus number of connected
components. Structural mass is the number of edges minus rank. It is the
accumulated submodular defect from the first experiment.

- If x and y differ, the two graphs are separate forests. Total mass is zero.
- If x and y agree, their union is a triangle. Total mass is one.

In both cases the edge sets are disjoint and individually massless, so

\[
M(A_x\cup B_y)=\Delta(A_x,B_y)
=\begin{cases}1&x=y,\\0&x\ne y.\end{cases}
\]

The contact condition thus follows from composition in the located graph.
It is not a table of particle masses. Spatial adjacency and the interpretation
of vertex labels at a site are still choices made for this model.

For a control, replace B's edge by (2,3). Even at the same site the union is
an open path, so its defect remains zero. Both controls use the same travel
rule; only the graph structure changes.

## 2. One rule for both objects

Each object has two direction components, R and L. Use the previous balanced
unitary mixer

\[
B=\frac12\begin{pmatrix}1+i&1-i\\1-i&1+i\end{pmatrix}.
\]

One step consists of:

1. Change the sign of the amplitude if the combined graph has odd defect.
2. Apply B to each object's direction components.
3. Move each object one site in its resulting direction.

In symbols,

\[
U=S(B\otimes B)D,\qquad
D|x,d;y,e\rangle=(-1)^{\Delta(A_x,B_y)}|x,d;y,e\rangle.
\]

This tests the simple real phase map n -> (-1)^n. The previous fixed-source
experiment used a different phase map. Neither phase map is selected by the
lattice axioms. The sign map distinguishes even and odd defects; it would
not distinguish masses zero and two without an extension.

D is a reversible sign change, the mixer is unitary, and S is a permutation
of basis states. Their product is therefore unitary. Both objects obey the
same mixer and shift. The rule is invariant under exchange of the two moving
positions/directions and under a common spatial translation.

The rank defect changes as the objects meet and separate. It is not a conserved
quantity in this evolution. Norm is conserved. The model conserves the two
components themselves: it has no rule that creates objects from a vacuum,
changes their internal edge sets, or creates additional objects.

## 3. Finite experiment and controls

The initial direction state is (RL - LR)/sqrt(2). This is an explicit preparation
of an entangled direction state; the experiment does not claim to create that
initial entanglement. The same preparation is used for every control.

The initial positions are either (0,0) or (-4,4). After 32 steps:

| Start | Can composition close a cycle? | Probability of separation at most 4 | Mean separation |
|---|---|---:|---:|
| Same site | Yes | 0.665191 | 12.548581 |
| Same site | No | 0.070892 | 27.926564 |
| Eight sites apart | Yes | 0.065732 | 28.321682 |
| Eight sites apart | No | 0.072161 | 28.364290 |

The closing pair prepared together retains much more probability at small
separation. Its center is not fixed: the center's second moment after 32 steps
is 49.785548. The mean center is zero by symmetry, so this measures spreading
of the center, not motion toward a fixed source.

The separated start does not show clear capture at this time. A high probability
of remaining close after starting together is not the same claim as distant
objects being attracted and forming a bound pair through collision.

The full state retains exact norm one at every tested step. Running the inverse
for 32 steps returns exactly the initial amplitudes. Translation and exchange
checks also pass. For the separated preparation, the interacting and free
states agree exactly for the first four steps, before the contact rule can act.

There is no finite spatial box, absorbing edge, or periodic wraparound.
Every finite-time state occupies a finite causal cone on the discrete line.

## 4. A bound pair that can travel

Finite-time concentration alone is not a proof of binding. We can also solve
the relative-motion equations.

Write the center coordinate as c=(x+y)/2 and the relative coordinate as
r=(x-y)/2. These are integers in the parity sector reached by the experiment.
Because the rule is invariant under common translations, use a center factor
exp(i K c), and solve for the relative amplitudes. This is a mathematical
representation of discrete translations, not an assumption of continuous
spacetime.

Let h=exp(iK), H=h+1/h=2 cos(K), and lambda be the one-step eigenvalue. Eliminating
the RR and LL components away from contact gives a two-component relative
mixer with coefficients

\[
f=\frac{\lambda H-2i}{\lambda(2\lambda-iH)},\qquad
a=\frac{f+i}{2},\qquad b=\frac{f-i}{2}.
\]

In the antisymmetric exchange sector, set the contact vector to
(RR,RL,LR,LL)=(0,1,-1,0). For positive relative position use

\[
v_r=(u,A,-\rho,v)\rho^{r-1},\qquad A=-i/\lambda,
\]

where

\[
u=\frac{2\lambda/h-2i}{2\lambda(2\lambda-iH)}(A-\rho),\qquad
v=\frac{2\lambda h-2i}{2\lambda(2\lambda-iH)}(A-\rho).
\]

The negative side is obtained by exchanging the two objects and changing the
sign. This use of an antisymmetric state is a mathematical sector choice,
not a derivation of fermion statistics for the two distinguishable components.

The incoming and outgoing matching equations are

\[
bA-a\rho=-\lambda,\qquad aA-b\rho=\lambda\rho A.
\]

They have the bound-band solution

\[
\boxed{\rho=\frac{\cos K}{3},\qquad
\lambda_\pm(K)=\pm\sqrt{1-\frac{\cos^2 K}{9}}
+\frac{i\cos K}{3}.}
\]

Both eigenvalues have modulus one. The absolute value of rho is at most 1/3,
so the relative probability tail falls by at least a factor 1/9 per successive
relative-coordinate step. Each such step corresponds to two sites of particle
separation. A zero value of rho gives a compact relative profile, with the
first tail site retained.

The denominators above do not vanish: lambda has nonzero real part, whereas
2 lambda = iH would have zero real part. Also 1-rho^2 is at least 8/9.
The two lambda roots are distinct for all real K.

The unnormalized relative vector has squared norm exactly six for every K.
The symbolic certificate checks the matching, stationary components, and norm
identities by reducing their rational numerators modulo

\[
3h\lambda^2-i(h^2+1)\lambda-3h=0.
\]

At K=0 the decay amplitude is 1/3 and the eigenvalues are
(+/-2 sqrt(2)+i)/3. The simulator independently verifies the recurrence and
normalization in an exact quadratic algebra. No numerical eigensolver is used
to certify that sector.

A single K mode is extended in the center coordinate. Superpositions across
the band form center-localized wave packets while maintaining bounded relative
spread. The eigenphase has nonconstant derivative:

\[
\left|\frac{d\arg\lambda}{dK}\right|
=\frac{|\sin K|}{\sqrt{9-\cos^2 K}}\leq\frac13.
\]

Thus the bound pair has a propagating band, with maximum group speed 1/3
site per time step for its center. This is a band speed, not a statement that
every initial state moves at that speed.

## 5. Exactly two thirds in the two bound bands

The initial same-site direction vector is (0,1,-1,0)/sqrt(2). Its inner product
with each normalized bound relative vector has squared magnitude 1/3, since
the contact entries are (0,1,-1,0)/sqrt(6). The two eigenvectors at each K are
orthogonal because their unitary eigenvalues are distinct.

The initial center is localized at zero, with uniform spectral weight in K.
It therefore has total projection weight 2/3 onto these two bound bands.
This projection is conserved by evolution. The statement concerns a spectral
component of the state; the probability of separation at most four is not
exactly 2/3 at every time. The finite-time table includes both that component's
tails and interference with the remaining component.

This supplies a persistent traveling composite sector without a fixed source.
It does not establish capture of arbitrary separated inputs, or the formation
of an elementary particle from a vacuum.

## 6. What this says about the proposal

Compared with the first experiment, composition now changes the defect during
motion. The same rule acts on both objects. A stable relative structure can
travel through the lattice without being held by an external source. These
are concrete mathematical properties of the model.

Several requirements remain separate:

- The poset does not select complex amplitudes, the probability rule, the
  direction mixer, spatial adjacency, or the sign phase. Those remain inputs.
- The mass being tracked is graph nullity. Identifying it with inertial mass
  requires a separate comparison with the model's dispersion and response.
- Components remain present and internally unchanged. This is not a theory
  of their creation, decay, or internal stability.
- Interaction is strictly at contact. There is no force between separated
  objects, no mediator, and no evidence here for universal gravitational motion.
- The one-cycle invariant does not produce the observed particle mass hierarchy.
- Two different submodular geometries can supply different interaction rules;
  this graph construction has not been selected uniquely by the thin category.

The matching two-particle contact-walk mechanism has existing precedents:
Ahlbrecht and collaborators studied moving bound molecules in interacting
quantum walks, using a defect in the relative-position coordinate.
This experiment connects such a contact rule to a particular submodular graph
defect; it is not a claim of a new binding mechanism. See their
[primary paper](https://arxiv.org/abs/1105.1051).

The next question is more specific than “can it bind?”: can the rank and
composition structure select a propagation rule, and can local interactions
between dynamical degrees of freedom produce a response at a distance?

The [travel-rule selection exploration](../travel_rule_selection/README.md) addresses
the first question with exact counterexamples, additional selection principles,
and Lean proofs. The response-at-a-distance question remains open.
