# Rotation thermodynamics on the associahedron

Builds on [thin-category-lattice.md](../../../thin-category-lattice.md), §§3.3, 4.0.1, 6.4.
Script: [rotation_thermodynamics.py](rotation_thermodynamics.py); raw output: `rotation_thermodynamics_results.json`.

Everything below was checked by exact enumeration for the stated sizes. Nothing here is a Lean proof yet.

## A. The pentagon obstruction is Kolmogorov's criterion

Let right rotations fire at rate `p` and left rotations at rate `q`. A finite Markov chain has an equilibrium (an energy `E` with `p/q = e^{-ΔE}` on each edge) **iff** the rate-ratio product around every cycle is 1 (Kolmogorov). Around a cycle that product is `(p/q)^σ(cycle)`. The paper's pentagon loop has `σ = −1`. So:

> For every `p ≠ q`, the biased rotation walk is a **non-equilibrium steady state**. `rotation_sign_no_vertex_potential` and `pentagon_sign_additive_quotient_trivial` say exactly that no energy function can restore detailed balance.

Dynamical witness: the steady rotation current `J_σ = ⟨dσ/dt⟩`. If σ had a vertex potential `h`, then `⟨dh/dt⟩ = 0` in any stationary state of a finite chain.

| leaves m | p/q | J_σ | entropy production | drift of a Loday potential |
|---|---|---|---|---|
| 5 | 1 | 0 | 0 | 0 |
| 5 | 2 | +0.081 | 0.056 | ~1e-15 |
| 8 | 2 | +0.298 | 0.207 | ~1e-14 |
| 8 | 5 | +0.339 | 0.546 | ~1e-14 |

Detailed balance holds only at `p = q`. A genuine potential (any linear functional of the Loday vector) has zero drift, as it must.

## B. Loday geometry is a collision rule, and it is the integrating factor

For a right rotation `((S T) U) → (S (T U))` with block sizes `s, t, u`:

```
Δv = s·u · (e_i − e_j),   i = gap(S|T) < j = gap(T|U),   Σ v = C(m,2) conserved
```

This was verified on every edge for m = 3…9 (5005 edges at m = 9). Each rotation moves along a **type-A root**, scaled by `s·u`.

Read the gaps as cells and `v` as occupation. Then each rotation is a binary collision that moves `s·u` quanta between two cells, with total occupation conserved.

- unit sign σ counts **collisions**: a path function, like heat
- the root-valued label counts **transfer**: a state function, exact by construction

So the paper's remaining question ("change the edge labels so they respect the path relations") has a canonical answer: label each rotation by its root displacement `s·u(e_i − e_j)`. σ is not exact because collision sizes are not uniform. On K₄ the two routes are 2 collisions of size 2 against 3 collisions of size 1, and both total `(2,0,−2)`.

(That Loday edges are parallel to roots `e_i − e_j` is known from generalized permutohedra. The new part is reading it as a collision rule and as the repair for §6.4.)

## C. Where curvature lives, and the exclusion-gas count

**2-faces.** Every 2-face is a pentagon (flux 1) or a square (flux 0):

| K_m | pentagons | squares |
|---|---|---|
| 4 | 1 | 0 |
| 5 | 6 | 3 |
| 6 | 28 | 28 |
| 7 | 120 | 180 |
| 8 | 495 | 990 |

The data fit `#pentagons = C(2m−4, m−4)` and `#squares = (m−4)/2 · C(2m−4, m−4)`. The totals agree with the standard dissection count. So the **fraction of curved plaquettes is 2/(m−2) → 0**: the curvature dilutes as arity grows. (These are conjectural closed forms, checked for m ≤ 8.)

**Open TASEP.** With injection and extraction rates α = β = 1, the exact steady state gives `Z_N / w(empty) = C_{N+1}` for N = 1…10. That is the number of vertices of `K_{N+2}`. This is a known result (Derrida–Domany–Mukamel; Shapiro–Zeilberger). It means the exclusion lattice gas and the associahedron share a state count.

## Open questions this raises

1. **Lean.** Kolmogorov failure follows from the existing pentagon theorem plus a reversibility lemma. The root-displacement identity is a short tree induction. Both look formalizable.
2. **Dynamics, not just counts.** Is there a bijection, TASEP configurations ↔ binary trees, under which particle hops become rotations and the TASEP current maps to `J_σ`?
3. **Collision-size statistics.** The histogram of `s·u` (see JSON) is a fixed property of each `K_m`. Its large-m limit is the "collision kernel" of this gas.
4. **Pentagon formula.** Prove `#pentagons(K_m) = C(2m−4, m−4)`.
