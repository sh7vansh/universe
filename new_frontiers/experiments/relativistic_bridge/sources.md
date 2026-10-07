# Primary sources for the relativistic bridge

Date: 2026-10-07. Scope: free relativistic matter and matter on a prescribed
metric. These sources do not derive this project's structural mass assignment
or its field equation. Equations below use units with hbar = c = 1.

## 1. The direct flat-space bridge

Arrighi, Facchini, and Forets explicitly define the one-dimensional Dirac walk
in Section II.A, equations (1), (6), and (7):

\[
C_\varepsilon=\exp(-i\varepsilon m\sigma_x),\qquad
T_\varepsilon=\exp(-\varepsilon\sigma_z\partial_x),\qquad
W_\varepsilon=T_\varepsilon C_\varepsilon.
\]

The evolution is exactly unitary at each finite lattice spacing. On smooth
fields, first-order expansion gives

\[
i\partial_t\psi=(-i\sigma_z\partial_x+m\sigma_x)\psi.
\]

The mass enters the directional mixing angle, not an overall scalar phase.
Both spatial and temporal spacing scale as epsilon; the dimensionless angle
is epsilon times the fixed continuum mass. Changing coin/shift order changes
terms beyond first order. This is a direct existing match for the project's
shift-times-mixer architecture.
[Discrete Lorentz covariance for Quantum Walks and Quantum Cellular Automata,
arXiv:1404.4499, Sec. II.A](https://arxiv.org/pdf/1404.4499).

The same paper proves only first-order covariance for the ordinary Dirac
walk under its discrete Lorentz transformations (Sec. III.D). Its exactly
covariant Clock QW is a different model; the name does not identify it with
our delayed-travel operator W_M.

For the operator-splitting Dirac walk, Arrighi, Forets, and Nesme prove
finite-time convergence. For initial data in H^(s+2), the H^s wavefunction
error is bounded by a constant times epsilon times elapsed time times the
initial H^(s+2) norm. The lattice comparison includes low-pass filtering,
sampling, normalization, and reconstruction. Thus a first-order local
expansion alone should not be described as a full arbitrary-data convergence
proof. The abstract's O(epsilon^2) observational discrepancy probability is
different from the O(epsilon) wavefunction norm error.
[The Dirac equation as a quantum walk: higher dimensions, observational
convergence, arXiv:1307.3524, Secs. III–VII](https://arxiv.org/pdf/1307.3524).

## 2. What the existing balanced coin does and does not establish

This paragraph is our algebraic application of the sourced construction,
not a theorem claimed by the papers. The existing balanced mixer is

\[
B=e^{i\pi/4}e^{-i(\pi/4)\sigma_x}.
\]

Removing its global phase gives precisely the Dirac-walk coin family at the
fixed angle theta = pi/4. Its exact lattice dispersion is

\[
\cos\omega(k)=\cos\theta\cos k.
\]

For 0 < theta < pi/2, the positive band has gap omega(0) = theta and
omega''(0) = cot(theta). A nonzero curvature is not by itself the relativistic
mass identification. At fixed theta = pi/4, taking a time step epsilon to zero
would send the nominal physical mass theta/epsilon to infinity. In the direct
smooth-field construction the zeroth-order operator must be the identity;
this fixed coin does not satisfy that condition on the full spinor space.

The controlled massive continuum bridge is the family theta = epsilon*m and
k = epsilon*p, with fixed physical m and p. Alternative envelopes,
stroboscopic limits, or finite-lattice interpretations require their own
mapping; they cannot be assumed equivalent to this limit.

## 3. The massive curved-space theorem needs grouping and encoding

Arrighi, Facchini, and Forets construct paired quantum walks: group nearby
spinors, encode them with a local unitary E, evolve with a larger local
unitary W, then decode. For a physical two-component field the paired coin
has four components. Smooth initial fields satisfy both external and internal
regularity. Their derivation assumes E and W analytic in position, time, and
epsilon, with zeroth-order compatibility

\[
E_0^\dagger W_0 X E_0=I\oplus U.
\]

After first-order compatibility, the limit is

\[
\partial_t\psi=A\partial_x\psi+\tfrac12(\partial_x A)\psi+iC\psi,
\qquad A=A^\dagger,\ C=C^\dagger,\ \|A\|\leq1.
\]

Their reconstruction procedure accepts such coefficient fields and produces
compatible coins and encodings. Equations (39)–(40) identify massive curved
Dirac coefficients in terms of a supplied metric/dyad. The lattice causal
cone must contain the physical one, possibly after rescaling coordinates on
a bounded region. This is a prescribed-background construction, with formal
continuum matching and numerical checks; the separate flat-space convergence
paper should not be silently promoted to a general curved-background theorem.
[Quantum walking in curved spacetime, arXiv:1505.07023, Secs. II–IV,
Eqs. (1), (19), (39)–(40)](https://arxiv.org/pdf/1505.07023).

## 4. An explicit lapse target and the higher-dimensional route

The higher-dimensional extension uses successive paired walks along spatial
directions. Its Hamiltonian has symmetrized derivative terms plus a local
mass/spin-connection term. It encompasses massive (3+1)-dimensional Dirac
propagation when the supplied tetrad fits inside the lattice causal cone.
[Quantum walking in curved spacetime: (3+1) dimensions, and beyond,
arXiv:1609.00305, Secs. IV–V](https://arxiv.org/pdf/1609.00305).

Our specialization of that Hamiltonian to a static one-dimensional lapse,
with flat dx probability measure and inverse dyad e^0_0 = 1/N,
e^1_1 = 1, e^1_0 = 0, is

\[
ds^2=N(x)^2dt^2-dx^2,\qquad
H_N=-i\sigma_z\bigl(N\partial_x+N'/2\bigr)+Nm\sigma_x.
\]

Take smooth positive bounded N and suitable boundary conditions. The N'/2
term ensures Hermiticity. The lapse multiplies both the derivative coefficient
and the rest-energy term. By inspection, an added identity potential V(x)I
changes neither derivative coefficient nor local propagation cone, so it does
not reproduce this metric coupling by itself. This comparison is our
inference from the Hamiltonian, not a gravitational-field derivation.

## 5. Correct scope of the previously cited discrete-metric paper

The 2018 Arrighi–Di Molfetta–Facchini paper addresses the (1+1)-dimensional
massless sector, especially a scalar component satisfying

\[
\partial_t\psi=c(t,x)\partial_x\psi+
\tfrac12\partial_x c(t,x)\psi.
\]

It constructs tunable transport speeds through grouped/encoded walks, including
finite sets of local coin operators. Metric parameters are still supplied.
Its interest in quantizing a metric is motivation and prospective work, not
an Einstein equation derived from matter. Cite it for discrete geometric
transport; cite the preceding paired-walk papers for massive curved Dirac.
[Quantum walking in curved spacetime: discrete metric, arXiv:1711.04662,
Introduction and Secs. III–VI](https://arxiv.org/pdf/1711.04662).

## 6. A finite-lattice alternative to taking spacing to zero

Bisio, D'Ariano, and Tosini study a different exact unitary Dirac automaton,
with a component that stays at a site while changing chirality:

\[
U(k)=\begin{pmatrix}ne^{ik}&-i\mu\\-i\mu&ne^{-ik}\end{pmatrix},
\qquad n^2+\mu^2=1,\qquad
\omega(k)=\arccos(n\cos k).
\]

Here mu is a dimensionless bounded mass parameter. For small mu and k,
the dispersion approaches sqrt(k^2+mu^2). One can hold the microscopic
lattice fixed and interpret ordinary particle wavelengths and masses as
small in lattice units. This avoids insisting that the lattice spacing is
physically infinitesimal; it still requires a small dimensionless mass and
momentum regime and does not make an arbitrary balanced coin exactly
continuum-relativistic. Its finite-lattice dispersion has corrections. It
also requires a mass parameter, so it supplies no automatic structural
nullity-to-mass theorem.
[Dirac quantum cellular automaton in one dimension: Zitterbewegung and
scattering from potential, arXiv:1305.0461, Sec. II,
Eqs. (2), (5)–(7)](https://arxiv.org/pdf/1305.0461).

## 7. The line cannot directly supply ordinary Einstein gravity

In two spacetime dimensions,

\[
R_{\mu\nu}=\tfrac12Rg_{\mu\nu},\qquad
G_{\mu\nu}=R_{\mu\nu}-\tfrac12Rg_{\mu\nu}\equiv0.
\]

Thus the ordinary Einstein equation with zero cosmological constant forces
T_mu_nu = 0 rather than furnishing a sourced local metric equation. A
cosmological term adds an algebraic constraint; it does not repair the missing
Einstein dynamics. This does not make prescribed curved metrics meaningless.
For dynamical lineal gravity, Jackiw explicitly introduces an additional
scalar/dilaton; for example, his Eq. (1) is the action integral of
sqrt(-g)*eta*(R-Lambda). Higher-dimensional gravity, or a dimensional
reduction retaining additional fields, provides other possible targets.
[Gauge Theories for Lineal Gravities, R. Jackiw,
arXiv:hep-th/9309082, Introduction and Eq. (1)](https://arxiv.org/pdf/hep-th/9309082).

## Research consequence

The smallest justified bridge is a mass-dependent mixing family with a shared
shift speed, followed by an explicit Dirac limit. Assigning m = kappa*M is
an additional structural law whose consequences can then be analyzed with
the established Dirac framework. Curved propagation next requires transport
coefficients that encode a metric. A source law for that metric remains
separate work; the existing Cartan minimization cannot inherit Einstein
dynamics merely from a successful matter-equation match.
