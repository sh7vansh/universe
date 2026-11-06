# Tested dimensionless physics catalogue for K6

## What this establishes

Twenty-six equation forms and operator identities have been constructed and checked. Several are equivalent formulations of the same dynamics, not independent discoveries. The matches concern actual operators, actions, conservation laws and gauge transformations, not renaming variables.

The paper supplies order, associahedral cells, roots, Cartan energy and path valuation. The earlier toy model supplies negative rotation links. Time, continuous fields, inner products, Hamiltonian evolution, noise, damping and extra potentials are additional assumptions. The numerical checks verify the stated finite model; they do not establish that this is physical spacetime or that the additional dynamics are Lean theorems.

The full complex has cell counts `[42,84,56,14,1]`, plus its empty face. Ordinary integer incidence coboundaries obey `d1 d0 = d2 d1 = d3 d2 = 0`. Numerical ranks give Betti numbers `[1,0,0,0,0]`, as expected for a filled convex polytope. We choose unit weights on all cells. Define

```text
L = d0ᵀd0 = 4I − adjacency(K6)
H₋ = D₋†D₋ = 4I + adjacency(K6), where (D₋ψ)_(s→t) = ψ_t + ψ_s
L1 = d0d0ᵀ + d1ᵀd1
C = A4 Cartan matrix = tridiagonal(−1,2,−1).
```

`L` is the ordinary graph Laplacian. `H₋` is a different, magnetic operator. `L1` acts on edge fields. `C` acts on four root coordinates, not on the 42 vertices.

## Complete checklist

Every row below passed the executable checks. Rows with added nonlinear or statistical laws are conditional model constructions rather than laws selected by the paper.

| # | Equation or identity | Dimensionless form | What was checked / what was added |
|---|---|---|---|
| 1 | Harmonic chain / Cartan wave | `q̈ + Cq = 0` | Analytic normal-mode evolution, energy conservation, acceleration; real coordinates and kinetic energy added |
| 2 | Graph wave | `q̈ + Lq = 0` | Spectral evolution including zero mode, acceleration, conserved energy; kinetic energy added |
| 3 | Spatially discrete Klein–Gordon | `q̈ + (L+μ²I)q = 0` | Massive mode evolution and energy; mass term added; no Lorentz symmetry inferred |
| 4 | Canonical Hamilton equations | `q̇=p; ṗ=−Cq` | Hamiltonian generator preserves symplectic form and energy; equivalent to row 1 |
| 5 | Damped wave / telegraph form | `q̈+γq̇+(L+μ²I)q=0` | Exact damped modes; `Ė=−γ||q̇||²`; damping added |
| 6 | Heat equation | `u̇=−Lu` | Mass, positivity, maximum principle and Dirichlet-energy decay; dissipative evolution added |
| 7 | Continuous-time random walk | `ṗ=−Lp` | Conservative nonnegative off-diagonal rates and edge-flux continuity; probabilistic meaning added |
| 8 | Poisson equation | `Lφ=ρ`, `Σρ=0`, `Σφ=0` | Pseudoinverse solves charge equation with fixed potential gauge; source and boundary convention added |
| 9 | Kirchhoff / electrostatic energy | `Lφ=ρ`; `ρᵀφ=||d0φ||²` | Node balance and positive effective resistances for all 84 edges; constitutive unit weights added |
| 10 | Magnetic Schrödinger | `iψ̇=H₋ψ` | Evolution derivative, norm and energy conservation; complex quantum evolution added |
| 11 | Quantum probability continuity | `ρ̇+d0ᵀJ=0` | Local balance at all 42 vertices; oriented current defined below |
| 12 | Ehrenfest identity | `d〈O〉/dt=i〈[H₋,O]〉` | Direct state derivative equals commutator for a vertex observable; no canonical position/momentum assumed |
| 13 | Source-free cellular Maxwell | `d0ᵀE=0; Ḟ+d1E=0; Ė=d1ᵀF; d2F=0` | Constrained trajectories, all identities and conserved energy; quadratic gauge action added |
| 14 | Maxwell with currents | `Ė=d1ᵀF−J`; `ρ̇=−d0ᵀJ`, `ρ=d0ᵀE` | Charge balance and field work `Ė_field=−EᵀJ`; source convention added |
| 15 | Temporal-gauge edge wave | `Ä+d1ᵀd1A=0`, `d0ᵀȦ=0` | Transverse edge trajectories; equivalent to source-free Maxwell |
| 16 | Cellular Hodge–Dirac | `Q=d+d†`; `Q²=d†d+dd†` | Exact integer matrix square on all 197 nonempty cells; cochain Hilbert space added |
| 17 | Supersymmetric quantum-mechanics algebra | `Q1=Q; Q2=iΓQ`; `Q1²=Q2²=H`; `{Q1,Q2}=0` | Exact graded algebra and numerical supertrace `Tr(Γe^(−tH))=1`; not particle supersymmetry |
| 18 | Hodge decomposition / longitudinal-transverse split | `a=d0φ+d1ᵀβ`, no harmonic edge component | Reconstruction and orthogonality; full filled-cell topology used |
| 19 | Nonlinear scalar / φ4 equation | `q̈+Lq+μ²q+λq³=0` | Independent finite-difference energy gradient and energy-balance identity; quartic potential added |
| 20 | Allen–Cahn gradient flow | `q̇=−Lq−λ(q³−q)` | Double-well energy gradient and `Ė=−||∇E||²`; double-well potential added |
| 21 | Gibbs canonical thermodynamics | `π=e^(−βE)/Z`; `S=log Z+β〈E〉` | Complete 198-state rank ensemble, derivative of `log Z`, nonnegative heat capacity; ensemble and energy choice added |
| 22 | Defect-energy master equation | `ṗ=Rp`, `Rπ=0` | Detailed balance, probability preservation and relative-entropy decay for a pinned-defect energy; reference vertex and Metropolis rates added |
| 23 | Antiferromagnetic Ising frustration | `E=Σ_edges s_i s_j`, `s_i=±1` | Exact enumeration of every square/pentagon spin state and transfer-matrix partition formula; classical spins and Ising coupling added |
| 24 | Compact gauge flux / Wilson loops | `W_f=exp(i(d1θ)_f)`; `E_W=Σ_f(1−Re W_f)` | All 56 face holonomies, local gauge invariance and facet Bianchi products; compact gauge energy added |
| 25 | Free-particle / paraxial shear flow | `(q,p)→(q+ep,p)`, `U(e)=[[1,e],[0,1]]` | Exact addition and symplectic identities for every integer pair in −5…5; same shear group as §6 |
| 26 | Open A4 Toda chain and Lax equation | `H_T=½Σp_i²+Σexp(q_i−q_(i+1))`; `L̇_T=[B_T,L_T]` | Energy gradient, Lax equality, conserved traces 1…5 and convergent integration; exponential potential added |

Primary references for the quantum, diffusion, Poisson, Klein–Gordon and gauge identifications are collected in [physics_sources.md](physics_sources.md). The graph magnetic operator is defined in [Fabila-Carrasco, Lledó and Post](https://arxiv.org/pdf/2010.08828); master/diffusion equivalence in [Goto and Hino](https://arxiv.org/pdf/1908.04535); Klein–Gordon action in [Tong's field-theory notes](https://www.damtp.cam.ac.uk/user/tong/qft/qfthtml/S1.html); cellular electrodynamics in [Stern et al.](https://authors.library.caltech.edu/records/pt0r8-amq73); graph Hodge–Dirac/index structure in [Post](https://arxiv.org/pdf/0708.3707). The double-well energy corresponds to [Chodosh's Allen–Cahn notes](https://web.stanford.edu/~ochodosh/AllenCahnSummerSchoolUConn2018.pdf). Exact Ising transfer matrices are given in [Edinburgh's notes](https://www2.ph.ed.ac.uk/~dmarendu/ASP/Section2.pdf).

## The added structures and their derivations

### Wave, heat and nonlinear fields share an energy but have different dynamics

The paper's Dirichlet construction generalizes to the rotation graph as `V(q)=½||d0q||²`. Its gradient is `Lq`. Adding kinetic energy gives `q̈=−Lq`; choosing dissipative gradient descent instead gives `q̇=−Lq`. Choosing complex Hamiltonian evolution gives a Schrödinger equation with that operator. These choices are not interchangeable predictions of the static energy.

Adding `μ²||q||²/2` yields the spatially discrete Klein–Gordon equation. Adding `λΣq_i⁴/4` yields the nonlinear scalar equation. Adding the double-well potential `λΣ(q_i²−1)²/4` and choosing gradient descent yields Allen–Cahn. The same linear part is structurally supported; none of these added potential functions is forced by the paper.

For quantum row 11 the code uses the incidence orientation convention

```text
ρ_v=|ψ_v|²
J_(s→t)=2 Im(conjugate(ψ_t) U_(s→t) ψ_s), U=−1
ρ̇+d0ᵀJ=0.
```

An outgoing physical-current convention reverses this stored edge current. Electric potential and charge signs likewise depend on the divergence convention; all code identities use one stated incidence orientation. The Poisson/Kirchhoff test uses `d0φ` as its oriented gradient field. Maxwell row 14 defines charge by `ρ=d0ᵀE`.

### Modular defect can generate thermal dynamics with additional choices

Fix one vertex v0. For any other full bracketing v, the paper gives `Δ(v0,v)=|S0∩Sv|−3`. Define

```text
E(v)=−Δ(v0,v), with E(v0)=0.
```

This gives energies 0,1,2,3 on K6's 42 vertices. The reference vertex is an explicit background choice. For every undirected rotation edge, choose rates

```text
r_(v→w)=exp[−β max(E(w)−E(v),0)]
π(v)=exp[−βE(v)]/Z.
```

The rate identity `π(v)r_(v→w)=π(w)r_(w→v)` follows by considering the two signs of the energy difference. The corresponding continuous-time master equation has π as equilibrium and decreases relative entropy `D(p||π)`. This is a genuine detailed-balance thermal equation using Δ, but its energy, reference and rates are supplied assumptions. It is not a proof that natural face rank is a physical energy.

A separate canonical model takes `E(C)=rank(C)` on all 198 completed faces. Its partition function is exactly

```text
Z(β)=1+42e^(−β)+84e^(−2β)+56e^(−3β)+14e^(−4β)+e^(−5β).
```

Then `〈E〉=−∂β log Z` and `C=β² Var(E)≥0`. At β=0.7, `Z≈50.309825973` and `C≈0.305630860`. Treating faces of different dimensions as microstates is an explicit ensemble choice.

### Frustration is a precise connection between the signs and energy

For added classical signs s_v=±1, the same negative link background gives `E=Σ s_v s_w`: every edge prefers opposite signs. A square permits that preference on all four edges; a pentagon cannot satisfy all five simultaneously.

Exact enumeration gives:

```text
square:    minimum energy −4,  2 ground configurations
pentagon:  minimum energy −3, 10 ground configurations.
```

The periodic antiferromagnetic partition function is

```text
Z_N=(2cosh β)^N+(−2sinh β)^N.
```

The code checks it against all 16 square and 32 pentagon configurations. These are classical Ising signs, not derived quantum particle spins. The fixed parity background also has compact Wilson energy 56, from 28 pentagons each contributing 2 and 28 squares contributing 0.

### The travel shear has an exact Hamiltonian meaning

The paper's `U2(e)` is already the matrix `[[1,e],[0,1]]`. On a phase-space pair `(q,p)` it is the flow of the dimensionless free Hamiltonian `H=p²/2` sampled at integer times:

```text
q̇=p; ṗ=0
q(t)=q(0)+tp(0); p(t)=p(0).
```

The same matrix is free propagation in paraxial ray optics, as derived in [MIT's photonics notes, equation (2.246)](https://ocw.mit.edu/courses/6-974-fundamentals-of-photonics-quantum-electronics-spring-2006/8e54d1625e9e71eb5b4e4998e6967e4e_chapter2.pdf). This interprets the existing monoid operation as sampled propagation; it does not identify the paper's separately assigned cost with physical time. Integer negative labels represent inverse flow.

### Type-A roots support an integrable Toda completion

Represent A4 simple roots as `α_i=e_i−e_(i+1)` in five-dimensional coordinates. Add exponential root interactions:

```text
H_T(q,p)=½Σ_i p_i²+Σ_(i=1)^4 exp(α_i·q)
q̇_i=p_i
ṗ_i=exp(q_(i−1)−q_i)−exp(q_i−q_(i+1)), omitting missing end bonds.
```

This is the open five-site Toda chain. With `a_i=½exp((q_i−q_(i+1))/2)`, `b_i=−p_i/2`, let L_T have diagonal b and adjacent entries a. Let B_T have upper adjacent entries a and lower entries −a. Direct differentiation gives

```text
L̇_T=[B_T,L_T]
d/dt Tr(L_T^k)=0, k=1,…,5
H_T=2Tr(L_T²).
```

The exponential energy is an added choice, rather than the paper's Cartan or face-rank energy. The root geometry is exactly the type required. The Lax form is the structure introduced by [Flaschka](https://doi.org/10.1103/PhysRevB.9.1924). The code verifies the signs, energy normalization, differential trace identities, and numerical integration at two step sizes.

## Important incompatibilities and unsupported extensions

1. **Magnetic diffusion:** `−H₋` is not a probability-conserving Markov generator. Heat/master equations use the ordinary L, or an explicitly constructed rate matrix.
2. **Curved versus flat derivatives:** ordinary cellular d obeys d²=0. Our parity links carry curvature; substituting their covariant derivative into the same filled-cell differential gives `d1 D₋≠0`. The code checks this obstruction. The flat supersymmetric complex and frustrated magnetic transport cannot be silently identified.
3. **Dirac and supersymmetry:** the constructed Q is Hodge–Dirac on cochains. There is no derived relativistic Clifford spinor, electron Dirac equation or Standard Model supersymmetry.
4. **Maxwell versus physical space:** the gauge/conservation algebra matches, but K6 is a four-dimensional cell complex. Unit cell weights and an external time coordinate do not establish a physical 3+1 geometry, metric or Lorentz invariance.
5. **Gravity:** no Einstein equation, dynamical metric, stress–curvature law or equivalence principle has been derived.
6. **Non-Abelian fields:** assigning matrices from a chosen group could construct further lattice gauge models, but K6 does not determine SU(2), SU(3), charges or coupling constants.
7. **Defect energy:** rank deficits are interaction corrections under a chosen valuation. They are not equal to the quadratic, quartic, Toda or Wilson energies above.
8. **Limits and completeness:** this is a finite catalogue of justified nearby structures, not all physics equations. Many constructions work on general graphs or cell complexes. K6's particular spectra, counts, face cycles and root labels provide the model-specific content.

## Verification and artifacts

Run `python3 math_project/experiments/physics_catalogue.py` with NumPy installed. The recorded run passed 951 checks across 26 equation/identity groups plus a structural cell-complex group. It constructs the actual graph and every cell boundary through dimension four, rather than using a guessed lattice.

Exact integer checks include all boundary-of-boundary identities, symplectic shear composition and cellular Dirac squares. Numerical checks cover spectra, trajectories, conservation, positivity, local continuity, detailed balance and gauge covariance. Independent finite differences check acceleration and energy gradients; Toda additionally has a step-size convergence check. Tolerances are stated in code. Most conservation residuals are near floating-point precision; finite differences are larger but pass their explicit tolerances. No empirical experiment or additional Lean proof was run.

Files:

- [Executable catalogue](physics_catalogue.py)
- [Machine-readable results](physics_catalogue_results.json)
- [Primary-source checks](physics_sources.md)
- [Earlier wave, quantum and Maxwell derivations](k6_physics_derivation.md)
- [Exhaustive modular-defect checks](modular_defect_energy.py)
