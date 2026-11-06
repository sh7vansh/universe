# Primary-source checks for structural physics correspondences

These references establish the physics-side operators. Whether the paper supplies the same operator must be checked against its actual definitions. A discrete operator alone does not force a time-evolution law.

## Harmonic-chain energy and wave dynamics

Nicola Manini's University of Milan teaching notes give nearest-neighbour quadratic elastic energy and derive Newton's equations by differentiating it. Setting both bond constants and masses to one produces the discrete wave equation `q̈_j = q_(j−1) − 2q_j + q_(j+1)`. The notes also distinguish classical normal modes from subsequent quantization. Source: [Phonons of a 1D chain](https://materia.fisica.unimi.it/manini/dida/1D-phonons.notes.html), energy and equations near the beginning.

For `n` internal coordinates with fixed endpoints `q_0=q_(n+1)=0`, the mathematical identity is

```text
V(q) = ½ Σ_(j=0)^n (q_(j+1)−q_j)² = ½ qᵀ C_n q
C_n = tridiagonal(−1, 2, −1)
q̈ = −C_n q.
```

The equality follows by expanding the squares. This is also the type-A Cartan matrix: simple roots `α_j=e_j−e_(j+1)` have Gram matrix `C_n`. MIT course notes discuss the root/Cartan construction: [Niven Achenjang, Fall 2020 Course Notes](https://www.mit.edu/~NivenT/assets/pdf/Fall_2020_Course_Notes.pdf), Lie-algebra/root-system lectures. Identifying the paper's matrix with `C_n` therefore gives an exact elastic stiffness correspondence, but kinetic energy and continuous-time variational dynamics remain extra assumptions.

## Connection Laplacian and magnetic Schrödinger operator

Milatovic defines a phase-deformed edge differential, its adjoint, and proves `Δ_σ=δ_σ d_σ` in equations (2.1), (2.8), and (2.9). Adding a real vertex potential produces a discrete magnetic Schrödinger operator. Source: [A Sears-type self-adjointness result for discrete magnetic Schrödinger operators](https://arxiv.org/pdf/1105.3129), §§1–2.

For a finite graph and unit-modulus links `U_vw=conjugate(U_wv)`, this specializes to

```text
E(ψ) = Σ_{undirected {v,w}} |ψ_v−U_vw ψ_w|²
(L_U ψ)_v = Σ_(w~v) (ψ_v−U_vw ψ_w)
E(ψ) = ψ†L_Uψ.
```

Fabila-Carrasco, Lledó, and Post explicitly define this operator in Definition 2.2 and state that constant edge phase π yields the signless Laplacian. Source: [Matching number, Hamiltonian graphs and discrete magnetic Laplacians](https://arxiv.org/pdf/2010.08828), §2.3. Thus the earlier rule assigning −1 to each rotation edge gives exactly `L_U=D+A`, not the ordinary `D−A`.

The dimensionless evolution `i ψ̇=L_U ψ` is the discrete magnetic Schrödinger form. The operator correspondence is exact; selecting Schrödinger evolution, a complex state space, and an inner product is an added dynamical completion, not a theorem about face ranks.

## Wilson-loop structure and its limits

David Tong's Cambridge notes construct lattice gauge link variables, their gauge transformations, products along closed paths, and a Wilson plaquette action. Source: [Gauge Theory, Chapter 4: Lattice Gauge Theory](https://www.damtp.cam.ac.uk/user/tong/gaugetheory/4lattice.pdf), §4.1, especially equations (4.8) and the Wilson-loop discussion.

With `U_e=−1`, path transport is `∏ U_e=(−1)^length=(−1)^σ`; pentagons have holonomy −1 and squares +1. This is exact Z₂ link-gauge/Wilson-loop structure. It does not derive physical spin, SU(2), a spatial metric, or a spacetime continuum limit.

Nontrivial pentagon holonomy forbids extension as a flat connection across the filled pentagon. It can be interpreted as discrete face flux; a nonflat connection can live on a simply connected region. Any continuum interpretation needs additional structure.

## Heat, random walks, and Gibbs detailed balance

Goto and Hino prove an exact equivalence between finite-state master equations with detailed balance and a weighted graph diffusion equation (Theorem 3.2); Theorem 3.1 gives the edge-current continuity form. Source: [Diffusion equations from master equations — A discrete geometric approach](https://arxiv.org/pdf/1908.04535).

The unweighted symmetric-rate specialization is `ṗ=−(D−A)p`. It preserves total probability and positivity. Edge transport phases must be omitted here: `−(D+A)` is not a conservative Markov generator. Taking vertex energies `E_v` and symmetric attempt rates `a_vw`, one admissible added rule is

```text
r_(v→w) = a_vw exp[−β(E_w−E_v)/2]
π_v = exp(−βE_v)/Z
π_v r_(v→w) = π_w r_(w→v).
```

Jianshu Cao's MIT notes give the master equation and detailed-balance relation with equilibrium probabilities: [Stochastic Processes and Brownian Motion](https://ocw.mit.edu/courses/5-72-non-equilibrium-statistical-mechanics-spring-2012/05d10d2e5952f3b91b10ba1305b46500_MIT5_72S12_master1.pdf), §§1.1.3–1.2. These assumptions produce thermal dynamics; pairwise modular defects alone are not a chosen vertex energy or rate law.

## Hodge–Dirac square and supersymmetric quantum mechanics

Olaf Post constructs the graph exterior derivative and `D=[[0,d†],[d,0]]`, with `D²=diag(d†d,dd†)`, paired nonzero spectra, and index `dim ker d−dim ker d†=|V|−|E|`. Source: [First order approach and index theorems for discrete and metric graphs](https://arxiv.org/pdf/0708.3707), §1, especially equations (1.1)–(1.4), Definition 1.1, and Lemma 1.2.

For an oriented cell complex, ordinary incidence coboundaries satisfy `d²=0`; hence `Q=d`, `Q†=d†`, and `H={Q,Q†}` are the algebra of supersymmetric quantum mechanics. The even-minus-odd heat trace is the Euler characteristic by cancellation of paired positive eigenvalues. Orientations, cochain state spaces, and inner products are extra chosen structures. This is a Hodge–Dirac operator, not the relativistic electron Dirac equation. Using a curved phase-twisted derivative across filled faces can break `d²=0`, so the ordinary cellular construction and the frustrated magnetic graph construction must not be conflated.

## Poisson / electrostatic equation

Tong derives the continuum electrostatic Poisson equation from `E=−∇φ` and Gauss's law: [Introduction and Electrostatics](https://www.damtp.cam.ac.uk/user/tong/em/el1.pdf), §1.2. The exact graph analogue uses an incidence gradient `d`, electric edge field `e=−dφ`, divergence `−d†`, and `L=d†d`, giving `Lφ=ρ`. A connected closed graph requires `Σρ=0` and a gauge choice such as `Σφ=0`; fixed boundary potentials instead produce a Dirichlet problem. Source charges, constitutive weights, and boundary conditions must be supplied.

## Klein–Gordon and damped wave forms

Tong explicitly derives `φ̈−∇²φ+m²φ=0` from quadratic kinetic, gradient, and mass terms: [Classical Field Theory](https://www.damtp.cam.ac.uk/user/tong/qft/qfthtml/S1.html), §1.1.1. Replacing the positive operator `−∇²` by a positive graph or Hodge Laplacian gives the exact spatially discrete form

```text
H(q,p) = ½pᵀp + ½qᵀ(L+μ²I)q
q̇=p; ṗ=−(L+μ²I)q
q̈+(L+μ²I)q=0.
```

Adding Rayleigh friction `γq̇` gives `q̈+γq̇+(L+μ²I)q=0`, a damped wave/telegraph form, with `Ḣ=−γ||q̇||²`. The derivation is finite-dimensional variational algebra. Kinetic energy, mass, and damping are additions. The correspondence does not supply Lorentz invariance, physical spacetime, or a relativistic continuum limit.

## Quantum continuity and Ehrenfest identities

Tong derives probability continuity from Schrödinger evolution: [Quantum Mechanics, Introduction](https://www.damtp.cam.ac.uk/user/tong/qm/qmhtml/S1.html), §1.2.2. For any Hermitian graph Hamiltonian, direct component differentiation yields

```text
ρ_v=|ψ_v|²
J_(v→w)=−2 Im(conjugate(ψ_v) H_vw ψ_w)
ρ̇_v+Σ_w J_(v→w)=0; J_(w→v)=−J_(v→w).
```

For a time-independent observable `O`, `d〈O〉/dt=i〈[H,O]〉`. Richard Fitzpatrick's UT Austin notes give Heisenberg evolution and its Ehrenfest application: [Ehrenfest Theorem](https://farside.ph.utexas.edu/teaching/qm/lectures/node33.html). The matrix identity holds on K₆ once a quantum Hamiltonian is selected; canonical spatial position and momentum relations are not implied on a finite graph.

## Z₂ gauge link energy

Chatterjee defines ±1 edge variables, face products, Gibbs weights, and Wilson loops explicitly in equations (1.1)–(1.3): [Wilson loops in Ising lattice gauge theory](https://arxiv.org/pdf/1811.09770), §1.1. On K₆'s cell structure the same form is

```text
W_f=product_(e∈boundary f) U_e
H_gauge=−Σ_f W_f
P(U)=exp(−βH_gauge)/Z.
```

Changing vertex gauge signs sends `U_vw→g_v U_vw g_w` and preserves every face product. Replacing square plaquettes with polygonal faces preserves this algebra, but changes the underlying statistical model. Making the previously fixed −1 links fluctuate and assigning this Hamiltonian are new assumptions. For fixed all-negative links, squares give `W=+1` and pentagons `W=−1`; this is a background flux pattern, not itself a derived field equation.

## The paper's U₂ shear: exact free propagation

MIT's photonics lecture notes derive the free-space ray-transfer matrix `[[1,L],[0,1]]` in equation (2.246), using `r_2=r_1+Lr'_1` and unchanged slope. Source: [Fundamentals of Photonics, Chapter 2](https://ocw.mit.edu/courses/6-974-fundamentals-of-photonics-quantum-electronics-spring-2006/8e54d1625e9e71eb5b4e4998e6967e4e_chapter2.pdf), §2.5, printed page 99. The same notes give propagation through a medium as upper-right entry `L/n`, illustrating dependence on the chosen canonical ray coordinates.

Consequently the paper's `U₂(e)=[[1,e],[0,1]]` is exactly the free-propagation ABCD matrix for dimensionless propagation parameter `e`. Independently, Hamilton's equations for `H=p²/2` integrate to

```text
q̇=p, ṗ=0
(q(t),p(t))ᵀ = [[1,t],[0,1]](q(0),p(0))ᵀ.
```

The integer-valued paper representation is the restriction of this flow to integer parameters; `U₂(e+f)=U₂(e)U₂(f)` is the propagation-composition law. Extending to real parameters and interpreting the vector as phase-space coordinates are additions. Negative labels describe inverse flow or signed transfer distance, rather than positive elapsed travel time by themselves. It is a linear shear, not a spatial rotation or general Lorentz transformation.

## Optional type-A nonlinear completion: the open Toda chain

Toda's original nonlinear-lattice paper is [Wave Propagation in Anharmonic Lattices (1967)](https://doi.org/10.1143/JPSJ.23.501). His own review explicitly concerns exponential nearest-neighbour interaction: [Development of the Theory of a Nonlinear Lattice (1976)](https://doi.org/10.1143/PTPS.59.1). Flaschka supplies the original conserved-integral construction: [The Toda lattice. II. Existence of integrals (1974)](https://doi.org/10.1103/PhysRevB.9.1924). A modern research source spells out the open Hamiltonian, transformed variables, Jacobi matrix, and skew matrix: [The Toda flow on Hessenberg elements of real, split simple Lie algebras](https://doi.org/10.1016/j.physd.2023.133810), introduction.

Using `N` coordinates and `N−1` type-A simple roots `α_i=e_i−e_(i+1)`, choose

```text
H = ½Σ_(i=1)^N p_i² + Σ_(i=1)^(N−1) exp(q_i−q_(i+1))
a_i=½ exp((q_i−q_(i+1))/2), b_i=−p_i/2
L_ii=b_i; L_(i,i+1)=L_(i+1,i)=a_i
B_(i,i+1)=a_i; B_(i+1,i)=−a_i.
```

Direct differentiation gives `ȧ_i=a_i(b_(i+1)−b_i)` and `ḃ_i=2(a_i²−a_(i−1)²)`, with `a_0=a_N=0`, so these specific conventions yield `L̇=[B,L]`. Trace cyclicity gives `d tr(L^k)/dt=0`. Source formulas vary in signs and scalings, so the commutator order must be checked with the chosen definitions. For `N=5` this uses A₄ roots and a five-coordinate open chain. The exponential potential and Hamiltonian dynamics are an optional completion; they do not follow uniquely from an A₄ Cartan matrix or from modular defects.
