# Can structural count select relativistic mass without supplying m=gM?

Date: 2026-10-07. Continuation of [the relativistic bridge](../relativistic_bridge/README.md).

There is a smaller, more explanatory principle than assigning a mass to every
count: **one unit of structure applies one common direction-mixing gate, and
independent contributions compose on the same direction state**. From this
principle, linear count dependence follows. The overall scale can be set to
one by choosing units. The composition principle itself is physical content;
the present graph/category assumptions do not yet establish it.

This exploration proves that implication in Lean, constructs an exactly
unitary rational example, and tests what the cycle space supplies on its own.
The result identifies a useful next axiom and a concrete bridge to the Dirac
generator. It does not derive that axiom from submodular rank.

## 1. What units remove, and what they leave

Write the common elementary mixing rate as g. In natural units, the proposed
rest mass is m(M)=gM. If g is positive, measuring time in units of 1/g makes
the numerical rate one. No separate SI calibration is needed to formulate
or prove the model.

But a unit change cannot select linear dependence instead of, for example,
m(M)=gM². The two rules predict different dimensionless ratios:

| Counts compared | Linear rule | Quadratic rule |
| --- | --- | --- |
| 2 versus 1 | 2 | 4 |
| 3 versus 1 | 3 | 9 |

Both rules can be inserted into an exactly unitary Dirac walk. Both depend
only on intrinsic count and respect graph isomorphisms. Therefore unitarity
and isomorphism invariance alone do not select one. A finite microscopic tick
also leaves a dimensionless parameter εg; rescaling units does not erase it.

The task is to justify why the contributions add, rather than to justify a
particular system of measurement.

## 2. A composition law derives the proportionality

Let C_n(ε) be the direction gate for structural count n. Suppose

\[
C_0(\varepsilon)=I,\qquad
C_{n+r}(\varepsilon)=C_n(\varepsilon)C_r(\varepsilon).
\]

Induction then forces

\[
C_n(\varepsilon)=C_1(\varepsilon)^n.
\]

If C_1(0)=I and C_1 is differentiable at zero, the matrix product rule gives

\[
C_n'(0)=nC_1'(0).
\]

With a single elementary direction-mixing generator

\[
C_1'(0)=-ig\sigma_x,
\]

the generator for every count follows:

\[
C_n'(0)=-ign\sigma_x.
\]

We have replaced a family of mass assignments by one gate and a composition
principle. There is no independently supplied count-dependent coefficient in
the elementary gate. This is still an added principle about the dynamics.

Count composition alone does not force exact exponential dependence on ε.
A continuous unitary time-group law would additionally give exponential
evolution via the standard generator framework. Our rational construction
below needs only differentiability and count composition.
See [the primary-source notes](sources.md) for that distinction
and for Dirac automata whose symmetry assumptions leave mass as a parameter.

### What selects the mixing direction?

For a two-direction state, assume its elementary Hamiltonian A is Hermitian,
commutes with direction exchange σ_x, and has trace zero. These conditions
force A=gσ_x for a real g. This classification is also proved in Lean.

Trace zero removes a scalar energy shift. Direction exchange selects the
mixing axis; it is an explicit symmetry condition. Neither condition forces
g to be positive or even nonzero. The physical positive rest energy is |g|n.
A positive common elementary scale can be chosen for the concrete model.

### What does “independent contributions” mean here?

The gates act successively on **one shared direction state**. Independent
quantum systems ordinarily have tensor-product state spaces. Their ordinary
combination does not automatically multiply gates on this shared factor.
The shared-factor coupling must therefore be specified and motivated.

Nor is the composition law a rule for every graph join. Independent cycle
spaces have additive dimensions, whereas the original lattice identity is

\[
M(A\vee B)+M(A\wedge B)=M(A)+M(B)+\Delta(A,B).
\]

The theorem is about addition of counts after those counts have been
established. It does not remove the earlier obstruction to treating a
pairwise join defect as an associative decoration of composition.

## 3. The graph supplies a canonical count, without a preferred cycle basis

Treat the undirected graph as a one-dimensional complex. Choose temporary
edge orientations and form the signed vertex–edge incidence matrix B. Its
cycle space is

\[
Z=\ker B,\qquad M=\dim Z=|E|-|V|+c,
\]

where c counts connected components. The orthogonal projector P_Z gives

\[
M=\operatorname{Tr}(P_Z)=\operatorname{Tr}(I_Z).
\]

Changing a cycle basis does not change P_Z. Relabelling vertices or reversing
edge orientations conjugates it by an orthogonal signed permutation. Its
trace is unchanged. This supplies the count used in the existing graph
specialization without declaring a particular list of loops fundamental.

However, the edge Hodge operator of this one-dimensional complex is BᵀB,
and it annihilates Z. Its cycles are zero modes. Their multiplicity supplies
M; it does not supply a nonzero mixing frequency. Adding filled faces would
change the complex and its harmonic modes, so we do not silently fill
triangles here.

### Available channels versus collective influence

The same cycle space supports two different couplings:

| Construction | Direction-mixing spectrum |
| --- | --- |
| gI_Z ⊗ σ_x on Z ⊗ ℂ² | ±g, each repeated M times |
| g Tr(I_Z) σ_x on the common ℂ² factor | ±gM |

In the first construction, there are M available internal channels. A
normalized internal state still produces mixing g, regardless of how many
channels are available. In the second, every internal dimension contributes
to one common generator; this is the extensive coupling we need.

Taking an unnormalized trace of the identity gives M. Taking a normalized
internal expectation gives one. These are different operations. Counting
available modes also differs from asserting M occupied constituents. Thus a
basis-free trace provides a clean way to *define* the collective coupling,
but does not derive it from the internal Hilbert space alone.

## 4. Local reversible internal travel need not depend only on M

On a simple cycle, use directed edges (u,v) as states and send each to (v,w),
where w is the unique neighbor of v other than u. This rule follows the
graph locally, retains both directions, chooses no preferred orientation,
and is a permutation, hence exactly unitary and reversible.

Its exact period is the cycle length:

| Graph | M | Directed-edge states | Exact period |
| --- | --- | --- | --- |
| Triangle | 1 | 6 | 3 |
| Square | 1 | 8 | 4 |
| Pentagon | 1 | 10 | 5 |

The characteristic polynomial for a cycle of length ℓ is
(λ^ℓ−1)². Even with locality, unitarity, and relabelling covariance, equal
cycle count need not imply equal internal travel spectra. Vertex Laplacians
also distinguish these graphs: the triangle has spectrum {0,3,3}, while
the square has {0,2,2,4}.

This is a counterexample to uniqueness of count-only internal dynamics. It
is not a calculation of translational inertia, and does not rule out a
different law that selects count-only mass. It establishes why that law
needs more than graph-isomorphism invariance.

## 5. An explicit compositional walk reaches the established Dirac generator

Use one rational elementary gate, with its scale set to one:

\[
R(b)=\frac{(1-b^2)I-2ib\sigma_x}{1+b^2},\qquad
C_n(\varepsilon)=R(\varepsilon/2)^n.
\]

Each elementary gate is exactly unitary. Its powers satisfy exact count
composition. Conditional translation uses the same tick for every count:

\[
U_n(\varepsilon,p)=e^{-i\varepsilon p\sigma_z}
R(\varepsilon/2)^n.
\]

The actual derivative at zero is

\[
U_n'(0,p)=-iH_n(p),\qquad
H_n(p)=p\sigma_z+n\sigma_x.
\]

The existing Dirac mathematics now supplies

\[
E_\pm(p)=\pm\sqrt{p^2+n^2},\qquad
E_+''(0)=1/n\quad(n>0).
\]

Thus the continuum generator has rest energy and curvature inertia n, and
one common limiting causal speed. Zero count removes mixing and leaves
chiral translation. It does not by itself establish photon properties.
Our Lean proof establishes exact finite-spacing unitarity and this actual
first derivative; it is not a theorem about convergence of iterated walks
to the full position-space Dirac evolution.

### This changes the finite-spacing rule

The previous bridge used R(εn/2). This exploration uses R(ε/2)^n. Their
first-order generators agree, but their finite-spacing gates differ:

\[
\theta_{\mathrm{previous}}=2\arctan(\varepsilon n/2),\qquad
\theta_{\mathrm{compositional}}=2n\arctan(\varepsilon/2).
\]

Only the second has exact count composition. The earlier rational coin and
its results remain intact; this is a new candidate microscopic rule.

Count composition also permits periodic responses. For example, four copies
of the unitary gate −iσ_x equal I. Consequently the infinitesimal linear
generator does not imply distinct finite-spacing masses at arbitrarily large
count. The relativistic statement uses fixed count and small spacing.

## 6. Verification and precise scope

[StructuralMixing.lean](../../../math_project/MathProject/StructuralMixing.lean)
formalizes:

- Count composition implies powers of one elementary gate.
- Additive scalar and matrix generators are linear in count.
- Hermitian, exchange-symmetric, traceless 2×2 generators have form gσ_x.
- The actual derivative of n repeated gates at the identity is n times the
  elementary derivative.
- Combining composition and symmetry gives the count-dependent Dirac mixing
  generator with a single remaining real coefficient.
- The concrete rational repeated gate has the selected generator, and its
  translated walk is exactly unitary with generator pσ_z+nσ_x.
- The identity trace counts dimensions; dividing by a nonzero dimension
  yields one.

The generic composition laws are hypotheses, not new Lean axioms. The
explicit rational construction satisfies them. The file compiles without
`sorry`; audited theorems use only standard core axioms, and the generic
monoid power theorem uses none. Energy and curvature results are reused from
[RelativisticBridge.lean](../../../math_project/MathProject/RelativisticBridge.lean).
Cycle-space geometry and the graph examples are exact Python certificates,
not general Lean graph theorems.

[The certificate](certificate.py) and
[recorded results](results.json) check:

- 25 count compositions and exact Gaussian-rational unitarity for counts 0–8.
- The old direct-count rational coin differs from the repeated elementary
  gate at count two; a quadratic count coin is also exactly unitary.
- Seven graph cycle projectors, their traces and nullspaces, alternative
  bases, and all 342 vertex relabellings with signed edge transport.
- Degenerate-channel and collective spectra for these examples.
- Local reversible directed-edge travel on cycles of lengths 3, 4, and 5,
  its exact periods and spectra, and every vertex relabelling in each case.
- The finite-gate periodicity example.

Reproduce from the repository root:

```bash
python3 -m new_frontiers.experiments.structural_mixing.certificate \
  --output /tmp/structural-mixing-results.json
cd math_project
lake build MathProject.StructuralMixing
```

## 7. Where this advances the research

The bridge can now be stated as a small package:

1. Use cycle-space dimension as the structural count.
2. Require count to be sufficient for the common direction response.
3. Require independent count contributions to compose on that shared state.
4. Choose one nonzero Hermitian, traceless elementary mixing generator with
   direction-exchange symmetry.

Linear relativistic mass then follows at the generator level. Existing
Dirac mathematics handles dispersion and inertia. The unresolved question
is the structural origin of steps 2–4, especially why all internal
contributions act coherently on one shared direction factor.

A useful next experiment would construct that factor and its coupling from
an internal graph update, then eliminate or average the internal degrees of
freedom. It must obtain the repeated-gate response or explain which
additional dynamical principle selects it; simply taking an unnormalized
trace would restate the proposed coupling. Compare equal-count graphs first,
because they directly test whether other internal data survive the reduction.

No particle species, changing-count collision law, bound-pair recovery,
curved transport, or dynamical gravitational equation is established by this
selection principle. Their limits remain as stated in the individual reports.
