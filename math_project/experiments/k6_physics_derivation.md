# Dimensionless physics equations from the paper's structures

## Result and logical status

There are exact structural matches to a harmonic-chain wave equation, a discrete magnetic Schrödinger equation, and cellular Maxwell equations. These are matches of energies, operators, gauge transformations and conservation identities, rather than changes of variable names. The paper supplies combinatorial and quadratic structures. Continuous fields, a time coordinate, inner products and a variational or quantum evolution principle are explicitly supplied modeling assumptions. No SI quantities are used.

The strongest energy identity already occurs in §5. The most direct completion of the earlier rotation transport is a magnetic graph Laplacian. The closest construction to the proposed ontology of matter on edges is the cellular gauge-field construction.

## 1. Cartan energy gives the discrete wave operator

The paper defines

```text
Q_n(q) = Σ_(j=0)^n (q_(j+1) − q_j)² = qᵀ C_n q
q_0 = q_(n+1) = 0
C_n = tridiagonal(−1, 2, −1).
```

Its formal domain is integer vectors. Extend the same polynomial to real coordinates. Add the dimensionless action

```text
S[q] = ½ ∫ (q̇ᵀq̇ − qᵀ C_n q) dt.
```

Euler–Lagrange variation then yields

```text
q̈ + C_n q = 0
q̈_j = q_(j−1) − 2q_j + q_(j+1).
```

This is precisely the fixed-endpoint harmonic-chain/discrete wave equation. The physical correspondence is documented in [Manini's harmonic-chain notes](https://materia.fisica.unimi.it/manini/dida/1D-phonons.notes.html). K6's facet labels use A4, so the relevant four-coordinate Cartan matrix has normal-mode frequencies

```text
ω_k = 2 sin(kπ/10), k = 1,2,3,4
    ≈ 0.618033989, 1.175570505, 1.618033989, 1.902113033.
```

These coordinates belong to the root-label space; they are not positions of the 42 graph vertices. The identity between Cartan stiffness and Dirichlet energy is supplied by the paper. Kinetic energy and time evolution are added. A continuum limit would require an increasing family of chains, spacing and time scaling; a single K6 does not supply that limit.

## 2. Rotation transport gives a magnetic Schrödinger operator

Let G be the undirected rotation graph of K6. It has 42 vertices, 84 edges and degree four at each vertex. Give an oriented edge e = s→t a link U_e, with |U_e|=1 and U_reverse=conjugate(U_e). Define

```text
(D_U ψ)_e = ψ_t − U_e ψ_s
H = D_U† D_U
Q_U(ψ) = Σ_edges |ψ_t − U_e ψ_s|² = ψ†Hψ.
```

This is the discrete magnetic/connection Laplacian, as defined in [Milatovic, equations (2.1), (2.8), (2.9)](https://arxiv.org/pdf/1105.3129). Choosing first-order complex Hamiltonian dynamics gives

```text
i ψ̇ = Hψ.
```

Our earlier parity rule assigns U_e = −1 to every elementary rotation, in both directions. Consequently

```text
H = 4I + adjacency(G)
i ψ̇_v = 4ψ_v + Σ_(w adjacent to v) ψ_w.
```

The plus sign is essential: this is the signless, rather than ordinary, Laplacian. Constant phase π gives exactly this operator in [Fabila-Carrasco, Lledó and Post, Definition 2.2 and Example 2.3](https://arxiv.org/pdf/2010.08828).

Local phase changes have the gauge law

```text
ψ_v → g_v ψ_v
U_(s→t) → g_t U_(s→t) conjugate(g_s).
```

The energy is invariant. For a time-independent connection, Hermiticity implies conservation of ψ†ψ and ψ†Hψ. A scalar amplitude already suffices; making ψ two-component with H⊗I merely duplicates the dynamics and does not derive spin.

Closed-path transport is

```text
W(loop) = product of edge links = (−1)^σ(loop)
pentagon W = −1; square W = +1.
```

This is exact Z2 link-gauge/Wilson-loop structure, consistent with the lattice link formulation in [Tong's gauge theory notes, §4.1](https://www.damtp.cam.ac.uk/user/tong/gaugetheory/4lattice.pdf). Nonzero holonomy prevents a flat extension across a face, but is valid face flux for a nonflat connection. A globally single-valued spatial orientation map is a stronger and different requirement.

The parity connection has no nonzero zero-energy state. If D_Uψ=0, neighboring amplitudes must have opposite signs; following an odd pentagon forces ψ=−ψ. Connectivity then forces ψ=0 everywhere. Numerically, the lowest eigenvalue of H is 0.8225903191. The ordinary connection has a constant zero mode. This spectral change follows from the chosen flux background; it is not a derived particle mass.

## 3. Edge and face incidence give cellular Maxwell equations

Orient K6's cells. Let B1 map edges to their endpoint boundaries, B2 map two-faces to their edge boundaries, and B3 map three-facets to their two-face boundaries. Define coboundaries

```text
d0 = B1ᵀ   : vertex values → edge values
d1 = B2ᵀ   : edge values   → two-face values
d2 = B3ᵀ   : two-face values → three-facet values.

d1 d0 = 0; d2 d1 = 0.
```

These are discrete gradient, curl, and the next exterior derivative. K6 gives matrices of dimensions 84×42, 56×84 and 14×56. Choose real edge fields A, vertex potentials φ, continuous time and equal cell weights:

```text
E = −Ȧ − d0φ
F = d1A
S[A,φ] = ½ ∫ (||E||² − ||F||²) dt.
```

The definitions and variation give the source-free equations

```text
d0ᵀ E = 0                 Gauss constraint
Ḟ + d1 E = 0             Faraday equation
Ė − d1ᵀ F = 0            Ampere equation
d2 F = 0                  magnetic Bianchi identity.
```

They have the exterior-calculus structure of source-free electromagnetism. This structure-preserving discretization principle is used in [Stern, Tong, Desbrun and Marsden](https://authors.library.caltech.edu/records/pt0r8-amq73). The transpose uses the supplied equal-weight inner products; a spatial metric would introduce Hodge/mass matrices. K6 is four-dimensional, so this alone does not identify it with three-dimensional physical space.

The equations are invariant under

```text
A → A + d0χ
φ → φ − χ̇.
```

Gauss's constraint is preserved because d0ᵀd1ᵀ=0. The energy ½(||E||²+||F||²) is conserved because

```text
EᵀĖ + FᵀḞ = Eᵀd1ᵀF − Fᵀd1E = 0.
```

In temporal gauge φ=0, the edge wave equation is

```text
Ä + d1ᵀd1 A = 0,
with d0ᵀȦ = 0.
```

This places the evolving field on the proposed matter edges. The signed face defect Δ is a different quantity: neither the Maxwell action nor Q_U follows from identifying Δ with energy. No equality between these energies and Δ is claimed. A physical theory using Δ as its primary energy still needs a total-energy construction and a dynamical principle. The greedy selection rule also does not, by itself, produce these equations.

## Reproducible verification

Run `python3 math_project/experiments/k6_physics_equations.py` (requires NumPy).

The script constructs every edge, all 56 two-faces and all 14 three-facets. It verifies both boundary-of-boundary identities exactly using integer incidence matrices. It checks gauge invariance, Faraday and magnetic Bianchi identities, Gauss-constraint preservation, energy conservation, the Cartan spectrum, unitary quantum transport, and all pentagon/square holonomies. The wave-energy drift across 101 analytic time samples was about 1.1×10⁻¹⁵. These checks establish this finite model's identities, not empirical validation or Lean formalization of the added physics.
