# Reaching an existing relativistic equation from structural travel

Date: 2026-10-07. Continues [the candidate universe](../proposed_universe/README.md),
following the user's proposal to establish a bridge to known physics and reuse
its mathematics instead of deriving every downstream result from scratch.

**Result:** the existing shift-and-mixer architecture can reach the free
one-dimensional Dirac equation. Put the structural count into a small
direction-mixing rotation, rather than only into a scalar phase or a travel
delay. With one common count-to-mass law, the continuum equation has mass
proportional to that count and a common limiting light speed. This is a
conditional construction: the new coupling is supplied, while the equation
and its consequences are derived.

There is also an established route from extended walks to Dirac propagation
on a prescribed curved metric. It tells us precisely what geometric transport
must change. Neither this construction nor the existing static Cartan field
supplies the Einstein field equation.

## Artifacts and reproduction

- [Primary-source research](sources.md).
- [Symbolic and executable certificate](certificate.py).
- [Recorded results](results.json).
- [Lean proofs](../../../math_project/MathProject/RelativisticBridge.lean).

Run from the repository root:

```bash
python3 -m new_frontiers.experiments.relativistic_bridge.certificate \
  --output /tmp/relativistic-bridge-results.json
```

SymPy is required, as in the earlier certificates. The core operator and
dispersion bridge is also formalized in Lean; its scope is specified below.
Existing experiments and their results are preserved.

From `math_project`, run:

```bash
lake build MathProject.RelativisticBridge
```

## Lean verification scope

The module compiles without `sorry`. Its audited theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`. In particular, the added
count-to-mass law is a definition, not a new Lean axiom.

| Claim | Lean declaration |
|---|---|
| Exact finite-spacing unitarity for the trigonometric walk | `walk_unitary` |
| Actual real-parameter derivative at zero spacing equals -iH | `walk_generator` |
| Hermitian Dirac Hamiltonian and H²=(p²+m²)I | `dirac_hermitian`, `dirac_square` |
| Characteristic polynomial and positive energy spectral root | `dirac_characteristic`, `positive_energy_spectral` |
| Rest energy m and actual second derivative E''(0)=1/m for m>0 | `energy_at_rest`, `energy_curvature` |
| Conditional count/rest/inertia identification | `count_rest_energy`, `count_inertia`, `lattice_inertia` |
| Original lattice defect/excess identity after the added coupling | `lattice_defect_excess` |
| Zero count removes mixing exactly | `zero_count_walk` |
| Exact rational coin/walk unitarity and the same derivative -iH | `rational_coin_unitary`, `rational_walk_unitary`, `rational_walk_generator` |

The matrix derivative uses the elementwise norm; in finite dimensions this
is a valid norm for local consistency. This proves first-order consistency
with the Dirac generator. It does not formalize finite-time iterated-walk
convergence, the full position-space PDE solution theory, the original balanced
coin's special-angle identity, or the finite-spacing quasienergy curvature.
Those remain mathematical arguments and/or Python/SymPy checks described below.
Metric transport and sourced gravity are also not formalized by this module.

## 1. The bridge already sits beside our mixer

Use the two direction amplitudes as a two-component field, and let sigma_x
exchange them while sigma_z has entries +1 and -1. Define

\[
C_\theta=e^{-i\theta\sigma_x},\qquad
S(k)=e^{-ik\sigma_z},\qquad U_\theta(k)=S(k)C_\theta.
\]

Our balanced mixer is exactly

\[
B=e^{i\pi/4}C_{\pi/4}.
\]

For an isolated fixed object, removing that common phase changes no
probabilities. Thus the operator architecture is already the one used in
the standard Dirac walk. This identity is verified symbolically. The sourced
Dirac construction is given in Section II.A of
[Arrighi, Facchini, and Forets, arXiv:1404.4499](https://arxiv.org/pdf/1404.4499).

An exact lattice identity is

\[
\det U_\theta=1,\qquad
\operatorname{tr}U_\theta=2\cos k\cos\theta,
\qquad \cos\omega=\cos k\cos\theta.
\]

The two eigenvalues are exp(+/-i omega). This dispersion is a useful bridge,
but it is not exactly the continuum relativistic dispersion at arbitrary
lattice momentum and angle.

For example, at theta=pi/4 the positive quasienergy is

\[
\omega(k)=\pi/4+k^2/2-k^4/6+O(k^6).
\]

A relativistic energy chosen to match that gap and curvature would instead be

\[
\sqrt{(\pi/4)^2+(\pi/4)k^2}
=\pi/4+k^2/2-k^4/(2\pi)+O(k^6).
\]

The fourth-order coefficients differ. This is a reproducible limitation of
an exact dispersion identification, not an exclusion of every possible
envelope or stroboscopic limit.

## 2. The controlled connection to Dirac

Introduce a common spatial spacing a and time step tau, with a/tau=c. To
avoid unit clutter take c=hbar=1, so a=tau=epsilon. A fixed physical momentum
p then has lattice momentum k=epsilon*p. Choose theta=epsilon*m, with fixed
m. The step becomes

\[
U_\varepsilon(p)=e^{-i\varepsilon p\sigma_z}
                    e^{-i\varepsilon m\sigma_x}
=I-i\varepsilon(p\sigma_z+m\sigma_x)+O(\varepsilon^2).
\]

After t/epsilon steps, its finite-time limit is generated by

\[
\boxed{i\partial_t\psi=
(-i\sigma_z\partial_x+m\sigma_x)\psi.}
\]

This is the free massive Dirac equation in one spatial dimension. Because
sigma_x and sigma_z square to the identity and anticommute,

\[
H(p)^2=(p^2+m^2)I,\qquad E_\pm(p)=\pm\sqrt{p^2+m^2}.
\]

Squaring the differential equation also gives the Klein-Gordon equation for
each component. For m>0, the positive energy expands as

\[
E_+(p)=m+\frac{p^2}{2m}+O(p^4),\qquad E_+''(0)=1/m.
\]

The same mass parameter therefore supplies rest energy and the small-momentum
inertial coefficient. The principal propagation speeds are +/-1 for every m.
These are consequences of the matched equation, not additional separate
inertia and speed postulates. Once the bridge is established in this regime,
the established free Dirac analysis can be used.

For the exponential coin, finite-time convergence on suitably regular data,
including how lattice sampling is compared to a continuum field, is addressed
by [Arrighi, Forets, and Nesme, arXiv:1307.3524](https://arxiv.org/pdf/1307.3524).
Their wavefunction norm bound is first order in spacing; their observational
discrepancy probability is second order. A formal local expansion alone is
not a convergence theorem for arbitrary sharply localized data.

This scaling can also be understood as an effective regime of a fixed
microscopic lattice: dimensionless mass and momentum are small in lattice
units. It does not require claiming that physical space is actually continuous.
The model still has finite-spacing corrections.

## 3. How structural count can enter, and what is chosen

For a stable graph G, retain the earlier intrinsic count

\[
M(G)=|E(G)|-r(G).
\]

Add one universal coupling law

\[
\boxed{m(G)=gM(G),\qquad \theta(G)=\varepsilon gM(G).}
\]

Here g is a common mass scale, not a coefficient separately fitted for each
named particle. The executable example chooses g=1 in model units. There is
no prediction of its physical value. With this law the limiting equation has
rest mass and curvature mass gM. It also specifies M=0: the two chiral
components propagate in opposite directions without mixing.

This replaces a specific part of the previous dynamics. It does not follow
from submodularity, thinness, or the previously imposed half-reflection law.
The half-reflection fixed theta=pi/4; the new family permits theta to vary.
Direction-exchange symmetry remains. The uniform direction ray is preserved,
but its vector acquires phase exp(-i theta), so exact uniform-vector fixing
is also relaxed.

Multiplying the coin by exp(+i theta) would restore that exact vector fixing.
For a uniform, fixed-count object, that is just an energy-reference shift.
For a space-dependent or coherently changing count it instead supplies an
additional scalar potential and cannot simply be discarded. A future
conversion theory must specify those relative phases.

This is the intended economy: choose a small law connecting count to one
operator, then inherit its tested relativistic consequences. It does not prove
that this law is required by the graph, or that gM equals an observed species
mass. In general M is not the pair defect Delta; their earlier restricted
relation still applies.

| Ingredient | Status |
|---|---|
| Graphic rank, intrinsic count, and defect/count identity | Earlier graph realization and algebra |
| Two amplitudes, probability rule, location, shift, common clock | Previously added quantum/spatial laws |
| Count controls directional mixing with one scale g | New coupling law |
| Dirac equation and common limiting light speed | Derived scaling limit |
| Relativistic rest energy and low-momentum inertia agree | Consequence of Dirac |
| Species, spin/statistics in 3+1 dimensions, field sourcing | Not obtained |

## 4. Exact rational realization and checks

Trigonometric amplitudes are unnecessary for an exact discrete realization.
Put b=epsilon*m/2 and use

\[
R_\varepsilon(m)=
\frac{(1-b^2)I-2ib\sigma_x}{1+b^2}.
\]

For real m this coin is exactly unitary. For rational epsilon and m, all
entries are Gaussian rationals. It is C_theta with
theta=2 arctan(epsilon*m/2)=epsilon*m+O(epsilon^3), hence has the same Dirac
generator. The common shift is still exactly one site per tick.

For bounded p and m, the one-step difference from the exact Dirac propagator
is O(epsilon^2). The difference introduced by replacing the exponential coin
with R is O(epsilon^3). Telescoping the products of unitary matrices bounds
the error after t/epsilon steps by O(t*epsilon). This gives a direct
finite-time convergence argument on a bounded momentum interval for this
rational variant. Extension to arbitrary continuum data requires regularity
and reconstruction assumptions; the script does not certify that extension.

Its positive physical band has, for m>0 and epsilon*m<2,

\[
E_\varepsilon(0)=\frac{2\arctan(\varepsilon m/2)}\varepsilon,
\qquad E_\varepsilon''(0)=\frac1m-\frac{\varepsilon^2m}{4}.
\]

Thus mass identification is exact in the limit, not at every finite spacing.
The same locality gives a strict common causal speed at finite spacing,
but exact continuum Lorentz invariance throughout the lattice spectrum is
not claimed.

The certificate verifies:

- Exact symbolic unitarity, determinant, dispersion, original-mixer identity,
  Dirac generator, and finite-spacing curvature.
- Exact Gaussian-rational norm, inverse evolution, and causal support for
  graph counts 0,1,2,3 over ten ticks at epsilon=1/8, using a normalized
  two-direction superposition. Different counts now change probabilities.
- Exact inverse/norm checks with a prescribed spatially nonuniform count.
  That profile is a background test, not a dynamical collision or graph change.
- Exact zero-count translation of an initially right-moving component.
- Floating-point finite-time propagator and dispersion comparisons for
  m=0,1,2,3,4 and p=-2,-1/2,0,1/2,2.

At time one, the maximum propagator Frobenius error over that grid is:

| Ticks per unit time | Error |
|---:|---:|
| 20 | 0.125395 |
| 40 | 0.061751 |
| 80 | 0.030755 |
| 160 | 0.015362 |
| 320 | 0.007679 |

The energy error decreases from 0.017814 to 0.00006988. These are numerical
diagnostics accompanying the symbolic identities and bounded-momentum argument.
They are not a finite-time exact continuum simulation or a claim about every
lattice momentum. The tested m=4 is an additional parameter value, not a
four-cycle configuration of the enumerated K4 graph.

## 5. Why the earlier clock is a different route

The previous W_M makes the whole local quasienergy branch E_0/M, up to its
clock-branch constants. Curvature decreases by 1/M, but every group velocity
decreases by that factor too. After choosing the same centered spectrum for
each count, its gap also decreases by 1/M.

The new construction holds the shift scale fixed and makes directional mixing
depend on mass. It approaches sqrt(p^2+m^2), where increasing m increases rest
energy and decreases low-momentum curvature while leaving the limiting light
cone unchanged. The clock's earlier curvature result remains correct; it is
not the same relativistic mass mechanism.

The new rule is also separate from the previous contact bound-pair walk.
Its bound bands and conserved bound projection cannot be transferred to this
modified mixer without a new calculation.

## 6. The next existing framework: prescribed curved Dirac

The massive curved-space construction is
[Arrighi, Facchini, and Forets, arXiv:1505.07023](https://arxiv.org/pdf/1505.07023).
It uses grouping/encoding and a larger local coin. Its continuum equation is

\[
\partial_t\psi=A\partial_x\psi+
\tfrac12(\partial_xA)\psi+iC\psi,
\quad A=A^\dagger,\quad C=C^\dagger,\quad\|A\|\leq1.
\]

The source note records the smoothness, encoding, and compatibility conditions.
Matching those hypotheses would allow use of the published construction;
our simple two-direction coin has not yet implemented its full variable-speed
transport. The previously cited
[arXiv:1711.04662](https://arxiv.org/pdf/1711.04662) concerns massless transport
and discrete metric choices, rather than being the massive curved theorem.

A concrete target is a static lapse metric

\[
ds^2=N(x)^2dt^2-dx^2,\qquad N>0.
\]

Specializing equations (39)-(40) of the massive paper, in the representation
with flat dx probability norm, gives

\[
\boxed{H_N=-i\sigma_z\left(N\partial_x+\frac{N'}2\right)
                 +Nm\sigma_x.}
\]

The derivative correction ensures Hermiticity with appropriate boundaries.
The lapse changes transport and rest energy together. Its local characteristic
speeds are +/-N. On a bounded region, the lattice causal cone must contain
these speeds; the published paired construction allows a common coordinate
rescaling to arrange this.

By contrast, a weak site phase exp(-i epsilon V(x)) supplies V(x)I in the
Dirac generator. It changes neither the derivative coefficient nor the
characteristic cone. It is a potential coupling, not by itself the lapse
metric above. The old finite parity/contact phase has not even been scaled
to this weak-phase limit, so it is not already a continuum field equation.

For a slowly varying lapse N=1+Phi, the positive-energy semiclassical symbol is

\[
H_+(x,p)=N(x)\sqrt{p^2+m^2}.
\]

At weak Phi and small p/m, its leading expansion contains
m+p^2/(2m)+mPhi. Hamilton's equations give leading acceleration -Phi',
independent of m. This is a weak-field, slowly varying, positive-band packet
diagnostic inherited from the prescribed metric, not an exact trajectory for
arbitrary Dirac states. The metric also specifies clock comparison
d tau=N dt and null coordinate speeds +/-N. These are known geometric
consequences we can reuse once the transport/metric bridge is supplied.

## 7. Where the Cartan field could enter

An explicit candidate connection to the earlier static source model is

\[
C_{A_L}\psi=\rho,\qquad N_i=1-\lambda\psi_i.
\]

For prescribed positive sources and sufficiently weak lambda>0 this gives
0<N_i<=1 and the leading probe potential -lambda*m*psi. With m=gM,
structural count then determines both kinetic inertia and this leading
potential coupling. The continuum curved equation would supply the
mass-independent response through geometry rather than through the previous
M-channel delay.

However, the count-to-mass law, field-to-lapse map, and use of the prescribed
Dirac metric are explicit model choices. This exploration has not constructed
the paired coins for that profile, established a field continuum scaling,
or evolved a quantum source. The Cartan equation is still prescribed-source
static minimization, not an Einstein equation or a propagating metric.

There is a dimensional issue that matters for choosing the next target:
in 1+1 spacetime the Einstein tensor is identically zero. Ordinary Einstein
gravity cannot directly provide a nontrivial sourced field equation on our
line. A higher-dimensional construction, dimensional reduction retaining
extra fields, or a specified lineal/dilaton gravity model is needed.
[Jackiw, Gauge Theories for Lineal Gravities, Introduction](https://arxiv.org/pdf/hep-th/9309082).
Prescribed curved propagation on a line remains a valid intermediate test.

## 8. What we can hand over to established mathematics

For stable free graph-count sectors, this exploration now gives an explicit
conditional route to Dirac. The source of the mass parameter is stated;
the limit, dispersion, and inertia relation are checked. Existing relativistic
matter theory can handle the consequences in that regime. It does not supply
the structural coupling automatically, a 3+1 particle interpretation, quantum
field statistics, or the metric source law.

The next concrete implementation is therefore prescribed geometric transport:
use the paired-walk construction to realize a smooth bounded lapse, verify its
curved-Dirac limit, and compare weak-field propagation and clock rates for
several graph counts. That completes the bridge for matter in a metric.
Choose the dimensional gravity target and source closure separately before
claiming that the metric is self-generated.

Subsequent exploration of the user's units objection is recorded in
[structural mixing](../structural_mixing/README.md). It replaces a direct
count-dependent mixing parameter with repetition of one elementary gate,
deriving linear count dependence from an explicit shared-direction
composition law. The new finite-spacing rule and its remaining structural
assumptions are stated there; the bridge above remains a separate model.
