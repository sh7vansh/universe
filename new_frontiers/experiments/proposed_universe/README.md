# Structural laws, allowed motion, and the mass/gravity tests

This continues [travel-rule selection](../travel_rule_selection/README.md). It states a
specific candidate universe so that the words mass and gravity can be tested
against its motion. It does not assume those identifications are true.

**Current status:** the phase-only inertia obstruction, contact controls, and
count/inertia comparisons remain active constraints. The static Cartan field
is an archived reference pending a dynamical gravity target. The imposed
M-channel clock repair is retired from the active mass program; its proved
properties are retained below for reproduction. The current mass route is
[structural mixing](../structural_mixing/README.md) through
[the relativistic bridge](../relativistic_bridge/README.md).

**Result:** the proposed laws give exact reversible motion, interference, and
moving bound pairs. Cycle defect does not equal the inertia of that motion.
The base laws provide a contact interaction, without a field between separated
objects. The existing Dirichlet-Cartan operator supplies a useful route to an
attractive static potential when a source law is added. That extension still
fails the universal-acceleration test if defect is used as its source and probe
charge while the travel law is left unchanged.

A separate, explicitly added **internal-clock law** repairs the kinetic test
for stable positive-count sectors: a count-M object has M clock channels and
travels once per completed clock cycle. Its low-momentum curvature mass is then
exactly M. Coupling that charge to the static field gives the same leading
acceleration for all such counts. This is a conditional constructive model,
not a derivation of the clock law from the original poset.

These are results about this explicit candidate, not a no-go theorem for every
physical model that could use the original framework.

## Read or reproduce

- [Exact checks](run.py), standard library only.
- [Exact results](results.json).
- [Dispersion certificate](certificate.py), requires SymPy.
- [Lean proofs](../../../math_project/MathProject/ProposedUniverse.lean).

From the repository root:

```bash
python3 -m new_frontiers.experiments.proposed_universe.run \
  --output new_frontiers/experiments/proposed_universe/results.json
python3 -m new_frontiers.experiments.proposed_universe.certificate
python3 -m new_frontiers.experiments.mobile_defects.certificate
cd math_project
lake build MathProject.DefectMassExploration
lake env lean MathProject/ProposedUniverse.lean
```

The simulator uses Gaussian integer amplitude numerators and exact rational
probabilities. The field checks use rational matrices. The dispersion checks
are symbolic identities. Clock identities and reversal are checked for counts
1 through 4. Lean proves the uniform-phase obstruction for every number of
steps and the three-site source-field algebra. The full dispersion calculus,
clock-spectrum construction, and general Green-function formula are not
formalized in Lean.

## 1. Candidate structural laws

There are two levels. The thin category describes inclusion and composition of
internal structures. Reversible time acts on a larger space of located objects
with direction records and amplitudes. Time evolution is not an upward arrow
in the thin category. Keeping that distinction permits reversible histories
without contradicting the uniqueness of parallel thin arrows.

| Law | Statement | Origin |
|---|---|---|
| Internal composition | An object is a finite graph edge set. Inclusion is the order; join is union and meet is intersection. | Chosen concrete realization of the existing lattice framework. |
| Rank and defect | Graphic rank is the number of independent edges. Define Delta(A,B)=r(A)+r(B)-r(A union B)-r(A intersection B). | Specialization of the existing submodular-rank definition. |
| Structural count | M(A)=number of edges minus rank. This is the number of independent cycles. The empty structure has M=0. | Modular-size minus submodular-rank construction from the earlier proofs. Calling this physical mass remains a hypothesis. |
| Location and clock | Space is the integer line. Each object has a site and two travel directions. One step advances a common integer clock. Internal edge sets and component number remain fixed. | Added model axioms. |
| Quantum states | Configurations have complex amplitudes; probabilities are squared norms. Joint components have a tensor-product direction space. | Added quantum axioms. |
| Local mixer | Exchange of directions is a symmetry; the uniform direction vector is fixed; two mixer substeps exchange directions. Choose the positive quarter-turn orientation. | Added selection principles; the numerical mixer follows from them. |
| Defect response | A unit cycle changes the phase nontrivially; two units restore it; phases multiply when counts add. Apply the resulting sign to the located union graph before mixing and shifting. | Added response principles selecting parity. |

The graphic rank and space are choices, not consequences of the associahedra.
This experiment does not assign the labels K0, K1, K2, ... to observed species.
In particular, graph cycle count and associahedron dimension are different
invariants. A particle interpretation would need stable modes and a demonstrated
relationship between their geometry and motion.

The pair defect is not an intrinsic single-object count. The two are related by

\[
\Delta(A,B)=M(A\cup B)+M(A\cap B)-M(A)-M(B).
\]

For edge-disjoint, individually cycle-free components, M of the union equals
their pair defect. This is precisely the situation in the bound-pair example.
For a general object, replacing every intrinsic M by an arbitrary pair defect
would make the value depend on its decomposition.

## 2. Derive the allowed motion

Let P be the projection onto the uniform direction vector. Direction exchange
symmetry and preservation of that vector give

\[
C=P+\xi(I-P).
\]

The two-substep law requires C squared to exchange the directions. Therefore
xi squared = -1, giving xi=i or -i. The stated orientation selects xi=i:

\[
B=\frac12\begin{pmatrix}1+i&1-i\\1-i&1+i\end{pmatrix},\qquad
B^2=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

For N located components, form the graph whose vertices are (site, internal
vertex label). Let M_loc be its cycle count. The defect-response laws select
D|configuration>=(-1)^M_loc |configuration>.

The resulting time step is

\[
\boxed{U_N=S_N B^{\otimes N} D_N.}
\]

S_N moves each component one site in its resulting direction. The order of
phase, mixer, and shift is part of the candidate laws. For N=0 the step is the
identity on the vacuum sector. No law creates components from the vacuum.

D is a unitary diagonal sign, B is unitary, and S is a basis permutation.
Their product is unitary, with inverse D* (B*) tensor N S inverse. Each object
moves at most one site per step. Common translations are symmetries. No fitted
particle constants appear. Reversibility follows, although conserved cycle
count does not.

This choice is now derived from a stated package of laws. The laws themselves,
including the phase orientation, are not derived from thinness alone.

## 3. Does defect produce inertial mass?

### An isolated object: an exact obstruction

An isolated object's internal cycle count is fixed. Its step is therefore

\[
U_M=(-1)^M U_0,\qquad U_M^t=(-1)^{Mt}U_0^t.
\]

The overall phase cancels from every position and direction probability.
This statement holds for arbitrary t and arbitrary preparation within the
fixed internal-object sector. Lean proves the general linear-operator version
and the coordinate-probability consequence. If a future theory allows coherent
conversion between internal sectors, relative phases can matter; that conversion
is absent here.

The exact experiment uses four different objects:

| Object | Cycle count M | Second position moment after 12 steps |
|---|---:|---:|
| Open tree | 0 | 5451/128 |
| Triangle | 1 | 5451/128 |
| Two-cycle graph | 2 | 5451/128 |
| Complete graph on four vertices | 3 | 5451/128 |

All position probabilities agree at every tested step, not only that moment.
All norms and inverse steps are checked exactly. Counts M and M+2 even have
identical phase responses, a second obstruction to a hierarchy of distinct
mass effects from the parity rule alone.

### Measure inertia from the travel spectrum

For the spatial mode exp(i k x), the single-object travel matrix is
diag(exp(-ik), exp(ik)) B. Its eigenvalues have the form

\[
\lambda=e^{i\pi/4}e^{\pm i\omega},\qquad
\cos\omega=\frac{\cos k}{\sqrt2}.
\]

Use the local branch E(k)=omega(k)-pi/4, so lambda=exp(-iE). Near k=0,

\[
E(k)=\frac{k^2}{2}+O(k^4),\qquad E''(0)=1.
\]

Define a **curvature mass** m_I=1/E''(0). This tests the coefficient of the
small-momentum kinetic term in site/step conventions. It is not an assertion
of invariant relativistic rest mass. Every isolated object above has m_I=1,
including the cycle-free object. Adding its intrinsic sign shifts quasienergy
by pi but leaves curvature unchanged.

The Fourier label k is a character of the discrete translation group. Its
continuous range is an analysis tool; neither space nor the update clock has
been made continuous.

### A bound pair: kinetic inertia does emerge, but differs from defect

The earlier cycle-closing pair has the exact bound band

\[
\lambda_+(K)=\sqrt{1-\cos^2K/9}+i\cos K/3.
\]

Taking E_b(K)=-arcsin(cos(K)/3) gives

\[
E_b''(0)=\frac{1}{2\sqrt2},\qquad m_{I,b}=2\sqrt2.
\]

This is a derived kinetic property of the persistent pair. The previously
certified normalized relative mode has probability 1/3 at contact. Its located
cycle count is one at contact and zero away, so its expected structural count
is 1/3, not 2sqrt(2). It is not an eigenstate of that count. A localized center
uses wave packets of these modes rather than a normalizable center plane wave.

There is a simpler nonconservation witness: the coincident antisymmetric
direction preparation has structural count exactly one. After one step it
has count exactly zero, while its probability norm remains one. Thus cycle
count is neither the inertial coefficient nor a conserved energy in this theory.
This is a property of the selected dynamics, not an inconsistency of the lattice.

## 4. Does the base motion produce gravity?

Located graphs at different sites use disjoint vertex labels. Their cycle
counts add. While two fixed components remain separated, D supplies only the
product of their isolated phases. The travel operator on that support is the
product of their free operators. There is no mediator, stored field, or source
term that changes another object's travel rule at a distance.

For the cycle-closing components, both isolated counts are zero. The interacting
and control states agree exactly until the contact phase can first act:

| Initial distance | States equal through step | First differing step |
|---:|---:|---:|
| 2 | 1 | 2 |
| 4 | 2 | 3 |
| 8 | 4 | 5 |
| 12 | 6 | 7 |

The earliest differing step follows from the maximum closing speed of two
sites per step and applying the contact phase before the next shift. The checks
compare full amplitudes, not approximate probability plots.

These laws support collision and binding, but no interaction between components
whose supports remain separated. This does not disprove locally mediated
gravity; it identifies the missing field or geometric degree of freedom in
this candidate. Labelling every traveled path as gravity does not supply that
interaction or its universal response.

## 5. Archived reference: static Cartan source extension

There is already a concrete mathematical bridge in FunctorialGeometry.lean:
cartanEnergy_eq_cartanMatrix identifies its Dirichlet energy with the A_n
Cartan matrix. On a finite line with zero boundary values the matrix is

\[
C_{ij}=2\delta_{ij}-\delta_{i,j+1}-\delta_{i,j-1}.
\]

Extend its field values to real numbers and add a source law:

\[
\mathcal E(\psi;\rho)=\tfrac12\psi^T C\psi-\rho^T\psi,
\quad\text{the static field minimizes }\mathcal E.
\]

Both the source coupling and the minimization principle are new axioms. Take
rho_i as a prescribed structural count at site i for this static comparison.
No rule for quantum-superposed sources is being assumed.

Varying each field value gives the entirely discrete source equation

\[
\boxed{C\psi=\rho.}
\]

For L interior sites and boundaries at 0 and L+1 its exact inverse is

\[
G_{ij}=\frac{\min(i,j)(L+1-\max(i,j))}{L+1}.
\]

For fixed j, this is linear on either side of j and vanishes at the boundaries.
Its second difference is zero off j and one at j, proving C G=I. The exact
script checks every entry for lengths 1 through 16. The three-site inverse is
also proved in Lean.

Write psi_0=G rho. Completing the energy gives

\[
\mathcal E(\psi_0+\eta;\rho)
=\mathcal E(\psi_0;\rho)+\tfrac12\eta^T C\eta,
\qquad \mathcal E_{\min}=-\tfrac12\rho^T G\rho.
\]

The Dirichlet quadratic form is positive definite, so the minimum is unique.
Lean proves the completion and minimum property for three sites. For two
positive sources q and Q the cross-energy is

\[
V(i,j)=-q Q G_{ij}.
\]

Holding the source at i fixed, this potential decreases as a probe approaches
i from either side. The extension therefore has an attractive static cross
potential on the finite line. Lean verifies the sign criterion.

This is an additional static field model. It is not derived gravity in U_N.
It has no field clock, local unitary propagation of the field, dynamical metric,
or joint matter-field evolution. Integrating out a static field is a nonlocal
effective calculation, not a finite-speed microscopic update. The line and
Dirichlet boundaries also give a different distance law from three-dimensional
Newtonian gravity. Position-dependent self-energy from the boundaries is
excluded from the probe cross-potential comparison.

## 6. Does the source extension pass universal acceleration?

In a weak external potential, a small-momentum packet with curvature
kappa=E''(0) has the leading diagnostic

\[
a\approx-\epsilon q\,\kappa\,\nabla\Phi,
\]

where Phi is the fixed background potential per unit probe charge. Epsilon
is a bookkeeping parameter for the weak-coupling comparison, not a fitted
particle constant. This uses the local kinetic expansion, not an exact
trajectory simulation of the coupled universe.

Universal acceleration would require

\[
q\,\kappa=\frac{q}{m_I}
\quad\text{to be independent of the probe's internal type.}
\]

If q is structural count M, the isolated objects have kappa=1, so the condition
fails. With eleven interior sites and a unit source at site six, the leading
right-side acceleration coefficients for probes with M=1 and M=2 are -1/2
and -1. Those exact coefficients compare the response in the same background;
they are not literal accelerations obtained from a finite-strength simulation.

Thus adding the Cartan source equation produces attraction but does not repair
the mismatch between defect charge and kinetic inertia. Assigning q=m_I by hand
would enforce the condition; it would not derive the proposed equality of
defect, inertia, and gravitational charge.

## 7. Archived mass candidate: internal clock length equals defect count

The failure above identifies a specific repair worth testing. Restrict to a
stable object with fixed positive internal cycle count M and add this law:

> The object has M internal clock channels. Each global tick advances one
> channel. Completing the channel cycle performs one base spatial travel step.

This replaces the isolated object's every-tick travel law. It is an additional
structural axiom relating topology to travel time. The channels are new memory
states; no canonical cycle basis or cyclic ordering has been extracted from the
graph. Therefore this construction shows consistency of a possible relation,
without establishing that graph composition requires it.

For a channel vector (v_0,...,v_{M-1}) define

\[
W_M(v_0,\ldots,v_{M-1})=(U_0v_{M-1},v_0,\ldots,v_{M-2}).
\]

The operator permutes channels and applies one unitary block. It is unitary and
local. After M ticks every channel has passed through that block once:

\[
W_M^M=\operatorname{diag}(U_0,\ldots,U_0).
\]

The exact script checks this operator identity on superpositions of all clock
channels for counts 1 through 4, along with norm and inverse evolution. Starting
in channel zero, position probabilities after t ticks equal the base walk after
floor(t/M) steps. Thus slower transport is an exact discrete consequence, before
using any momentum approximation.

If U_0(k)v=mu(k)v and lambda is a W_M eigenvalue, the channel equations give
v_q=lambda^(-q) v_0 and lambda^M=mu(k). Therefore, for the base local band E(k),

\[
E_{M,j}(k)=\frac{E(k)+2\pi j}{M},\qquad j=0,\ldots,M-1,
\quad E_{M,j}''(0)=\frac1M,
\quad\boxed{m_I=M}.
\]

This general channel argument derives the spectrum. The symbolic certificate
also checks the characteristic polynomials for M=1 through 4, using
det(lambda I-W_M)=det(lambda^M I-U_0), and verifies the curvature formula.

If the probe charge in the static source model is the same M, and a weak
potential acts at every global tick on all its clock channels, then

\[
q\,E_{M,j}''(0)=M\frac1M=1.
\]

The leading acceleration diagnostic is independent of count. In the same
eleven-site background used above, its coefficient is -1/2 for M=1,2,3,4.
This is the specific sense in which structural count, kinetic inertia, and
universal static-field response can be made compatible without SI constants.

The placement of that potential response matters: applying it only when the
clock wraps would divide its effective charge by M and lose this result.
Applying it every tick is an added coupling law. No coupled-field trajectories
are claimed by the algebraic diagnostic.

There are substantial limits. A zero-count object needs a separate propagation
law, so this does not yet give a photon. A collision that changes located count
cannot simply change the number of clock channels; a unitary conversion law
between internal sectors is missing. The earlier bound-pair contact model and
this clock repair are therefore separate constructions, not one completed
interacting theory. The band speeds also scale as 1/M; no common relativistic
dispersion or invariant rest-mass relation has been established. The source
field remains static, and no observed species or mass ratios follow.

## 8. What the next structural theorem would need to establish

The most useful target is now precise. For a stable mode with structural count
M, derive its travel spectrum and show

\[
E_M''(0)\propto\frac1M
\]

for positive M, with a separately specified propagation law for M=0. If the same
M then sources and couples to a dynamical field, universal response becomes a
testable consequence rather than a name assigned to the path.

The phase-only rule cannot achieve this target for isolated objects: its
all-time obstruction is proved. The clock extension achieves the target
conditionally, by postulating a structural delay. To derive it from the
original framework, a replacement must construct the internal travel channels
and their update law from the graph or category itself. A rule relating that
spectrum to nullity is still needed; nullity alone does not specify the graph's
connectivity or its travel operator. Choosing new mixing coefficients
separately for named particles would skip this structural step.

The source extension also needs a local field evolution and consistent
matter-field backreaction before it can model gravitational dynamics. The
existing Cartan energy is a candidate field operator, not that entire theory.

Discrete walks supporting bound composites have an established precedent in
Ahlbrecht and collaborators' [Bound Molecules in an Interacting Quantum Walk](https://arxiv.org/abs/1105.1051).
Arrighi, Di Molfetta, and Facchini show how local walk operators can represent
prescribed metric-related transport in [Quantum walking in curved spacetime:
discrete metric](https://arxiv.org/abs/1711.04662). These primary sources support
using discrete walks as mathematical physics models. Neither establishes this
proposal's defect/inertia identification or a self-generated gravitational
field from these axioms.

The candidate has therefore produced a useful distinction: interaction defect,
kinetic inertia, and field source are separately defined mathematical quantities.
A successful physical interpretation must demonstrate their required relation.
