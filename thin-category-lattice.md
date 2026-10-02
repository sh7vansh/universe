# The Categorical and Geometric Structure of Subobject Lattices

**Author:** Shivansh Singh  
**Date:** March 2026  
**Formalization:** Machine-checked in Lean 4 (Mathlib-compatible, zero unproven axioms)

---

## Abstract

We study the algebraic, categorical, and geometric structure of partially ordered sets and subobject lattices. By formulating a poset $(L, \le)$ as a thin category, we develop a unified framework spanning three core areas:

1. **Order and Homological Defects:** We realize meets and joins as universal categorical products and coproducts, and characterize submodular rank defects $\Delta(A, B) \ge 0$, showing that $\Delta$ vanishes identically if and only if modularity holds.
2. **Filtrations and Path Valuations:** On covering chains, we define a path valuation into the monoid $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$ combining traversal cost with unipotent shear transport. For semi-Artinian objects in abelian categories, we construct transfinite Loewy filtrations and prove finite/ordinal stabilization, complete object reconstruction, and the vanishing of directed residual colimits.
3. **Polyhedral and Root Geometry:** We analyze morphism compositions through the Tamari lattice $\mathcal{T}_4$ and construct an explicit bijection between the 9 boundary facets of the 3D Stasheff associahedron $K_5$ and the 9 almost-positive roots $\Phi_{\ge -1}(A_3)$, verified under the positive-definite $A_3$ Cartan metric.

All definitions, constructions, and theorems are formally machine-checked in Lean 4 with zero `sorry` placeholders and no non-standard axioms.

---

## 1. Introduction

Partially ordered sets $(L, \le)$ and subobject lattices $\mathrm{Sub}(X)$ are foundational objects across algebra, order theory, and representation theory. While lattices are classically studied through algebraic binary operations $(\wedge, \vee)$, many of their structural features—universal bounds, chain compositions, submodular defects, transfinite filtrations, and higher associativity—are naturally expressed through category theory and geometric combinatorics.

This paper presents a formal categorical and geometric study of subobject lattices, organized around five key components:

1. **Thin Categories and Universal Properties (§2):** We formulate a poset as a thin category $\mathcal{C}_L$, translating order-theoretic meets, joins, and closure operators into categorical products, coproducts, and idempotent monads.
2. **Submodular Defects and Modularity (§3):** We analyze submodular rank functions $\mathrm{rk} : L \to \mathbb{Z}$ via their defect $\Delta(A, B) = \mathrm{rk}(A) + \mathrm{rk}(B) - \mathrm{rk}(A \vee B) - \mathrm{rk}(A \wedge B)$, proving that non-negativity $\Delta \ge 0$ holds universally and that $\Delta = 0$ characterizes lattice modularity.
3. **Path Valuations on Covering Chains (§4):** We equip covering paths with valuations taking values in the monoid $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$, pairing strictly increasing step costs with upper-triangular unipotent shear transport.
4. **Transfinite Loewy Filtrations (§5):** In well-powered abelian categories with colimits, we construct transfinite Loewy sequences for semi-Artinian objects, proving ordinal stabilization at length $\Omega$, complete object reconstruction ($C_\Omega = \top$), and the vanishing of the directed colimit of residual cokernels.
5. **Associativity Posets and $A_3 \leftrightarrow K_5$ Root Duality (§6–§7):** We analyze higher parenthesizations through the Tamari lattice $\mathcal{T}_4$ (cardinality $C_3 = 5$) and establish an explicit constructive bijection between the 9 boundary facets of the 3D Stasheff associahedron $K_5$ and the 9 almost-positive roots $\Phi_{\ge -1}(A_3)$, verified under the positive-definite $A_3$ Cartan metric.

All definitions, constructions, and theorems in this paper are machine-checked in Lean 4 without unproven axioms or `sorry` placeholders.

---

## 2. Posets as Thin Categories

### 2.1 The Categorical Formulation

Let $(L, \le)$ be a partially ordered set. The associated category $\mathcal{C}_L$ is defined by:
- **Objects:** $\mathrm{Ob}(\mathcal{C}_L) = L$.
- **Morphisms:** For any $x, y \in L$, the hom-set $\mathrm{Hom}_{\mathcal{C}_L}(x, y)$ contains a unique arrow $\iota_{x, y}$ if $x \le y$, and is empty otherwise.
- **Identities and Composition:** Identity morphisms $\mathrm{id}_x = \iota_{x, x}$ follow from reflexivity ($x \le x$), and composition $\iota_{y, z} \circ \iota_{x, y} = \iota_{x, z}$ follows from transitivity ($x \le y \le z \implies x \le z$).

**Proposition 2.1 (Subsingleton Hom-Sets and Morphism Collapse).**  
*In any thin category $\mathcal{C}_L$:*
1. *Every hom-set $\mathrm{Hom}(x, y)$ is a subsingleton ($|\mathrm{Hom}(x, y)| \le 1$).*
2. *All parallel morphisms are equal: $f, g : x \to y \implies f = g$.*
3. *Every morphism is simultaneously a monomorphism and an epimorphism.*
4. *Any endomorphism is the identity: $f : x \to x \implies f = \mathrm{id}_x$.*
5. *If $x \le y$ and $y \le x$, then $x \cong y$. Any extension with a retraction splits trivially: $p \circ f = \mathrm{id}_y$ and $f \circ p = \mathrm{id}_x$.*

### 2.2 Universal Constructions: Limits and Colimits

When $L$ is a bounded lattice $(L, \wedge, \vee, \bot, \top)$, order operations coincide with categorical limits and colimits:

| Order-Theoretic Construct | Categorical Concept in $\mathcal{C}_L$ | Universal Property |
| :--- | :--- | :--- |
| Bottom element $\bot$ | Initial object $\mathbf{0}$ | Unique arrow $\bot \to x$ for all $x \in L$ |
| Top element $\top$ | Terminal object $\mathbf{1}$ | Unique arrow $x \to \top$ for all $x \in L$ |
| Meet $x \wedge y$ | Binary Product $x \times y$ | $z \le x \wedge y \iff (z \le x \land z \le y)$ |
| Join $x \vee y$ | Binary Coproduct $x \amalg y$ | $x \vee y \le z \iff (x \le z \land y \le z)$ |
| Infimum $\bigwedge S$ | Small Limit $\varprojlim S$ | Greatest lower bound for diagram $S$ |
| Supremum $\bigvee S$ | Small Colimit $\varinjlim S$ | Least upper bound for diagram $S$ |

### 2.3 Galois Connections and Closure Monads

A monotone map $F : L \to M$ between posets is canonically a functor $\mathcal{C}_L \to \mathcal{C}_M$.

**Definition 2.2 (Galois Adjunction).** A pair of monotone maps $F : L \to M$ and $G : M \to L$ forms a Galois connection ($F \dashv G$) if and only if:
$$F(x) \le y \iff x \le G(y) \quad \forall x \in L, y \in M$$
Categorically, this is an adjunction between thin categories:
$$\mathrm{Hom}_{\mathcal{C}_M}(F(x), y) \cong \mathrm{Hom}_{\mathcal{C}_L}(x, G(y))$$

**Proposition 2.3 (Closure Operators as Idempotent Monads).**  
*The composite $T = G \circ F : L \to L$ defines a closure operator satisfying:*
1. *Extensivity: $x \le T(x)$ for all $x \in L$.*
2. *Monotonicity: $x \le y \implies T(x) \le T(y)$.*
3. *Idempotency: $T(T(x)) = T(x)$ for all $x \in L$.*

*Categorically, $(T, \eta, \mu)$ is an idempotent monad on $\mathcal{C}_L$, whose category of algebras is the subposet of closed elements $\mathrm{Fix}(T) = \{x \in L \mid T(x) = x\}$.*

---

## 3. Submodular Rank Defects and Modularity

### 3.1 The Submodular Defect

Let $(L, \wedge, \vee)$ be a lattice. A rank function $\mathrm{rk} : L \to \mathbb{Z}$ is *submodular* if $\mathrm{rk}(A \vee B) + \mathrm{rk}(A \wedge B) \le \mathrm{rk}(A) + \mathrm{rk}(B)$ and *monotone* if $A \le B \implies \mathrm{rk}(A) \le \mathrm{rk}(B)$.

**Definition 3.1 (Submodular Defect).** For any pair $A, B \in L$, the submodular defect is:
$$\Delta(A, B) = \big(\mathrm{rk}(A) + \mathrm{rk}(B)\big) - \big(\mathrm{rk}(A \vee B) + \mathrm{rk}(A \wedge B)\big)$$

**Theorem 3.2 (Non-Negativity and Modularity).**
1. *Non-negativity:* For any submodular rank function, $\Delta(A, B) \ge 0$ for all $A, B \in L$.
2. *Modularity Criterion:* $\Delta(A, B) = 0$ if and only if the modular equality holds on $\{A, B\}$:
   $$\mathrm{rk}(A \vee B) + \mathrm{rk}(A \wedge B) = \mathrm{rk}(A) + \mathrm{rk}(B)$$
3. *Global Modularity:* If $\mathrm{rk}$ is a modular rank, then $\Delta(A, B) = 0$ identically across $L$.

### 3.2 $\mathrm{Tor}_0$ in Thin Categories

In the thin category substrate, the zeroth derived tensor product $\mathrm{Tor}_0(A, B)$ corresponds to the maximal shared subobject—the categorical meet $A \wedge B$:
$$\mathrm{Tor}_0(A, B) := A \wedge B$$
It satisfies symmetry $\mathrm{Tor}_0(A, B) = \mathrm{Tor}_0(B, A)$, associativity $\mathrm{Tor}_0(\mathrm{Tor}_0(A, B), C) = \mathrm{Tor}_0(A, \mathrm{Tor}_0(B, C))$, and the universal property $C \le A \land C \le B \implies C \le \mathrm{Tor}_0(A, B)$.

*(Context: In an ambient abelian category, the Mayer-Vietoris sequence $0 \to \mathrm{Tor}_1(X/A, X/B) \to A \cap B \to A \oplus B \to A + B \to 0$ gives the dimension-theoretic defect $\Delta(A, B) = \dim \mathrm{Tor}_1(X/A, X/B)$, explaining why modularity corresponds to the vanishing of derived intersection strain.)*

---

## 4. The Travel Functor $\mathbb{T}$ on Covering Quivers

Complementing the vertical extension data ($\mathrm{Ext}^*$) and horizontal intersection data ($\mathrm{Tor}_*$), the **Travel Functor** $\mathbb{T}$ captures the dynamic experience of moving along paths in the lattice substrate.

### 4.1 Covering Chains and Path Valuations

For a locally finite lattice $(L, \le)$, let $\mathcal{Q}_L$ be its covering quiver, with directed edges $x \to y$ whenever $y$ covers $x$ ($x \lessdot y$, meaning $x < y$ with no element strictly between them).

The Travel Functor $\mathbb{T} : \mathcal{P}(\mathcal{Q}_L) \to (\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$ assigns to each covering path $\gamma = (x_0 \lessdot x_1 \lessdot \dots \lessdot x_k)$ two independent accumulated invariants:
1. **Search Action $\mathcal{S}(\gamma) \in (\mathbb{N}, +)$:** Cumulative step costs $\sum_{i=0}^{k-1} c(x_i \lessdot x_{i+1})$.
2. **Unipotent Shear Transport $\mathbf{Trans}(\gamma) \in \mathbf{U}_2(\mathbb{Z})$:** The 2D upper-triangular matrix tracking extension classes:
   $$\mathbf{Trans}(\gamma) = \prod_{i=0}^{k-1} \begin{pmatrix} 1 & e(x_i \lessdot x_{i+1}) \\ 0 & 1 \end{pmatrix} = \begin{pmatrix} 1 & \sum e_i \\ 0 & 1 \end{pmatrix}$$

### 4.2 Monoid Structure and Strict Growth

**Definition 4.1 (Travel Experience Monoid).** We define the state space $\mathbf{Trav} = \mathbb{N} \times \mathbf{U}_2(\mathbb{Z})$ with identity and binary composition:
$$\mathbf{1} = (0, \mathbf{I}), \qquad (S_1, T_1) \cdot (S_2, T_2) = (S_1 + S_2, T_1 \cdot T_2)$$

**Theorem 4.2 (Monoid Axioms and Action Growth).**
1. *Monoid Laws:* Composition on $\mathbf{Trav}$ is associative and unital:
   $$\mathbf{1} \cdot t = t, \quad t \cdot \mathbf{1} = t, \quad (a \cdot b) \cdot c = a \cdot (b \cdot c)$$
2. *No Free Travel:* For any step $s = (x \lessdot y)$ with non-zero cost $c(s) > 0$, the accumulated action strictly increases:
   $$\mathcal{S}(t \cdot s) > \mathcal{S}(t)$$

---

## 5. Transfinite Loewy Filtrations and Basis Discovery

### 5.1 The Loewy Length Existence Theorem

Let $\mathcal{A}$ be a well-powered abelian category with colimits. An object $U_0 \in \mathcal{A}$ is *semi-Artinian* if for every proper subobject $C < U_0$, the residual quotient $\mathrm{coker}(C \hookrightarrow U_0)$ contains a simple subobject.

**Definition 5.1 (Cellular Loewy Sequence).** The cellular Loewy sequence is constructed transfinitely:
- **Base Case:** $C_0 = \bot$.
- **Successor Step:** $C_{\alpha+1} = C_\alpha$ if $\mathrm{coker}(C_\alpha \hookrightarrow U_0) = 0$; otherwise, choose a simple subobject $a \hookrightarrow \mathrm{coker}(C_\alpha)$ and pull it back to form $C_{\alpha+1} = \mathrm{pb}(a \to \mathrm{coker}(C_\alpha))$.
- **Limit Ordinal:** $C_\lambda = \sup_{\beta < \lambda} C_\beta$.

**Theorem 5.2 (Loewy Length Existence and Reconstruction).**  
*Because the subobject lattice $\mathrm{Sub}(U_0)$ is small, the strictly increasing transfinite sequence $C_\alpha$ must stabilize. Consequently:*
1. *There exists an ordinal $\Omega$ such that $C_\Omega = \top = U_0$.*
2. *The inclusion morphism $C_\Omega \hookrightarrow U_0$ is an isomorphism.*
3. *The filtered colimit of the residual diagram vanishes:*
   $$\varinjlim_{j \in J} \mathrm{coker}(C_j \hookrightarrow U_0) = 0$$

### 5.2 Well-Founded Basis Selection

In a discrete complete lattice $L$ generated by an indexed set $\{e(j) \mid j \in J\}$ under a well-founded priority order $(J, \le)$, the greedy choice function:
$$\phi(x) = \min_{<} \{j \in J \mid e(j) \not\le x\}$$
is well-defined for all $x < \top$. It satisfies the **novelty property**: $e(\phi(x)) \not\le x$, guaranteeing strict progress at every transfinite step toward $\top = \bigvee_{j} e(j)$.

---

## 6. The Crystalline Tower and the $A_3 \cong K_5$ Duality

### 6.1 The Crystalline Tower ($K_0 \longrightarrow K_\infty$)

When composing chains of morphisms in the thin category substrate, the non-uniqueness of parenthesizations yields an infinite, rigid polyhedral hierarchy: the **Crystalline Tower of Stasheff Associahedra $K_n$**, corresponding to the Cartan-Killing root systems $A_{n-2}$:

| Level | Discrete Chain Length | Vertices ($C_{n-1}$) | Lie Root Space | Boundary Facets | Order-Theoretic & Categorical Meaning |
| :---: | :--- | :---: | :---: | :---: | :--- |
| **$K_0$** | **0-Chain** ($\varnothing$) | $1$ | $A_0$ | $0$ | **Initial Object $\bot$** (Empty chain $\varnothing$, unique initial arrow) |
| **$K_1$** | **1-Chain** $\{x_0\}$ | $1$ | $A_0$ | $0$ | **Identity Morphism $\mathrm{id}_{x_0}$** (Trivial path, travel $\mathbb{T} = (0, \mathbf{I})$) |
| **$K_2$** | **2-Chain** $\{x_0 \le x_1\}$ | $1$ | $A_1$ | $0$ | **Covering Arrow ($x_0 \lessdot x_1$)** (Elementary morphism / 1-step gluing) |
| **$K_3$** | **3-Chain** $\{x_0 \le x_1 \le x_2\}$ | $2$ | $A_1$ | $2$ Vertices | **Composed Path $[0, 1]$** (2 bracketings of composition / homotopy) |
| **$K_4$** | **4-Chain** | **$5$** | **$A_2$** | **$5$ Edges** | **Tamari Lattice $\mathcal{T}_4$** (5 bracketings of 4 objects / Mac Lane pentagon) |
| **$K_5$** | **5-Chain** | **$14$** | **$A_3$** | **$9$ Facets (6 Pent + 3 Sq)** | **3D Associahedron** (14 bracketings / $A_3$ Cartan root space) |
| **$K_n$** | $n$-Chain | $C_{n-1} = \frac{1}{n}\binom{2n-2}{n-1}$ | $A_{n-2}$ | Cluster Variables | $(n-2)$D Universal Discrete $A_\infty$ Operad |

#### Base Elements and Identity Paths ($K_0 \to K_1$)
The foundational levels $K_0$ and $K_1$ anchor the operad directly in the thin category axioms:
1. **Initial Object ($K_0$):** The bottom element $\bot \in L$ (the 0-chain $\varnothing$). In $\mathcal{C}_L$, it is the initial object characterized by the universal property $|\mathrm{Hom}(\bot, x)| = 1$ for all $x \in L$.
2. **Identity Morphisms ($K_1$):** A 1-chain $\{x_0\}$ corresponds to the trivial 0-step path $\mathrm{id}_{x_0} : x_0 \to x_0$. Under the Travel Functor, $\mathbb{T}(\mathrm{id}_{x_0}) = (0, \mathbf{I})$ (zero search effort, identity unipotent shear matrix).
3. **Tamari Pentagon ($K_4$):** For $n=4$, the 5 bracketings of 4 objects form the Tamari lattice $\mathcal{T}_4$ ordered by right-associativity moves, with cardinality exactly $C_3 = 5$.

### 6.2 The $A_3 \leftrightarrow K_5$ Root Duality Theorem

For $n=5$, the 3D associahedron $K_5$ has 14 vertices and exactly **9 boundary facets** (6 pentagonal and 3 square faces).

In Lie theory, the $A_3$ root system contains 6 positive roots $\Phi^+(A_3)$ and 3 negative simple roots $-\Delta(A_3)$, forming the 9 almost-positive roots $\Phi_{\ge -1}(A_3)$:
- **Positive Roots (6):** $\alpha_1, \alpha_2, \alpha_3, \alpha_1+\alpha_2, \alpha_2+\alpha_3, \alpha_1+\alpha_2+\alpha_3$.
- **Negative Simple Roots (3):** $-\alpha_1, -\alpha_2, -\alpha_3$.

**Theorem 6.1 (Facet-Root Equivalence).**  
*There exists an explicit constructive bijection $\Xi : \Phi_{\ge -1}(A_3) \xrightarrow{\sim} \mathrm{Facets}(K_5)$ mapping:*
1. *The 6 positive roots bijectively to the 6 pentagonal facets:*
   $$\alpha_1 \mapsto P_0, \; \alpha_2 \mapsto P_1, \; \alpha_3 \mapsto P_2, \; \alpha_{12} \mapsto P_3, \; \alpha_{23} \mapsto P_4, \; \alpha_{123} \mapsto P_5$$
2. *The 3 negative simple roots bijectively to the 3 square facets:*
   $$-\alpha_1 \mapsto S_0, \; -\alpha_2 \mapsto S_1, \; -\alpha_3 \mapsto S_2$$

---

## 7. The $A_3$ Cartan Metric and Quadratic Form

The geometry of the $A_3$ root space $\mathbb{Z}^3$ is governed by the Cartan matrix:
$$C(A_3) = \begin{pmatrix} 2 & -1 & 0 \\ -1 & 2 & -1 \\ 0 & -1 & 2 \end{pmatrix}$$
inducing the symmetric bilinear form $\langle u, v \rangle_{A_3} = u^T C(A_3) v$.

### 7.1 Sum-of-Squares and Positive Definiteness

**Theorem 7.1 (Positive Definiteness).**  
*For every vector $v = (v_1, v_2, v_3) \in \mathbb{Z}^3$, the quadratic form $\langle v, v \rangle_{A_3}$ satisfies the sum-of-squares identity:*
$$\langle v, v \rangle_{A_3} = v_1^2 + (v_1 - v_2)^2 + (v_2 - v_3)^2 + v_3^2$$
*Consequently:*
1. *Positive semi-definiteness: $\langle v, v \rangle_{A_3} \ge 0$ for all $v \in \mathbb{Z}^3$.*
2. *Positive definiteness: $\langle v, v \rangle_{A_3} = 0 \iff v = 0$.*

### 7.2 Geometric Invariants of the Roots

Evaluating the Cartan form on the roots reproduces the fundamental geometric invariants:
1. **Norm Invariance:** All 6 positive roots have identical squared norm:
   $$\langle \alpha, \alpha \rangle_{A_3} = 2 \quad \forall \alpha \in \Phi^+(A_3)$$
2. **Adjacent Shear Coupling:** Adjacent simple roots form a $120^\circ$ angle with pairing:
   $$\langle \alpha_1, \alpha_2 \rangle_{A_3} = -1, \qquad \langle \alpha_2, \alpha_3 \rangle_{A_3} = -1$$
3. **Orthogonal Decoupling:** Non-adjacent simple roots are orthogonal:
   $$\langle \alpha_1, \alpha_3 \rangle_{A_3} = 0$$
4. **Coupled Composite Strain:** Activating composite roots satisfies the bilinear expansion:
   $$\langle \alpha_1 + \alpha_2, \alpha_1 + \alpha_2 \rangle_{A_3} = \langle \alpha_1, \alpha_1 \rangle + \langle \alpha_2, \alpha_2 \rangle + 2\langle \alpha_1, \alpha_2 \rangle = 2 + 2 - 2 = 2$$

---

## 8. Lean 4 Formalization and Machine Verification

The entirety of the mathematical development presented in Sections 2–7 is formalized in Lean 4 as the standalone, self-contained module [`FunctorialGeometry.lean`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean) within the `MathProject` workspace.

### 8.1 Design Principles and Axiomatic Foundations

The formal development follows three structural principles:
1. **Categorical Integration with Mathlib:** Rather than using ad-hoc posetal order structures, thin categories and subobject lattices are expressed directly through Mathlib's native category theory library (`CategoryTheory.Subobject`, `CategoryTheory.Abelian`, and `CategoryTheory.Limits`).
2. **Constructive Computational Core:** Discrete and algebraic structures—including the travel monoid $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$, the Tamari poset $\mathcal{T}_4$, the $A_3 \leftrightarrow K_5$ root-facet bijection, and the Cartan quadratic form—are defined constructively with `DecidableEq` instances and verified by computation (`rfl`, `ring`).
3. **Controlled Non-Constructivity:** Classical reasoning (`Classical.choice`) is strictly quarantined to points where the ambient mathematics fundamentally demands it: selecting simple subobjects in non-constructive abelian categories (Theorem 5.2) and invoking well-founded choice over infinite generator candidate sets (Section 5.2).

An automated axiom audit via `#print axioms` confirms that the entire formalization relies exclusively on Lean's core foundational axioms (`Classical.choice`, `Quot.sound`, `propext`), containing zero unproven axioms and zero `sorry` placeholders.

### 8.2 Paper-to-Code Correspondence Matrix

| Paper Statement | Mathematical Concept | Lean 4 Declaration | Proof Technique / Tactic |
| :--- | :--- | :--- | :--- |
| **Proposition 2.1** | Subsingleton homs, monic/epic collapse, split extensions | [`thin_mono`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L75), [`thin_epi`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L81), [`thin_extension_splits`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L91) | `Subsingleton.elim` |
| **Section 2.2** | Meets as categorical products, joins as coproducts | [`meet_universal`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L122), [`join_universal`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L130), [`subobject_mono`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L144) | `le_inf`, `sup_le`, `inferInstance` |
| **Proposition 2.3** | Closure operators as idempotent monads | [`ClosureOperator`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L102), [`ClosureOperator.toFunctor`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L109) | Posetal functorial lift |
| **Theorem 3.2** | Submodular defect $\Delta \ge 0$, modularity criterion $\Delta = 0$ | [`submodularDefect`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L167), [`defect_nonneg`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L171), [`defect_zero_iff_modular`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L178) | `linarith` |
| **Section 3.2** | $\mathrm{Tor}_0$ realized as categorical meet | [`tor0`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L193), [`tor0_comm`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L195), [`tor0_universal`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L201) | Infimum symmetry and universal properties |
| **Theorem 4.2** | Travel monoid laws and strict action growth | [`Unipotent2`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L215), [`TravelExperience`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L246), [`comp_assoc`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L267), [`action_strictly_increases`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L296) | Upper-triangular matrix arithmetic, `linarith` |
| **Theorem 5.2 (1–2)** | Loewy length existence $\Omega$, stabilization, top reconstruction | [`loewySequence_mono`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L432), [`loewy_length_exists`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L462), [`reconstruction`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L474), [`reconstruction_iso`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L478) | `Ordinal.limitRecOn`, `eventuallyConst`, `Subobject.top_arrow_isIso` |
| **Theorem 5.2 (3)** | Vanishing residual colimit $\varinjlim \mathrm{coker} = 0$ | [`residualDiagram`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L486), [`residual_colimit_vanishes`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L502) | Filtered colimit absorption, `isZero_cokernel_of_epi` |
| **Section 5.2** | Well-founded basis selection and novelty property | [`candidates_nonempty`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L535), [`fixedPriorityPhi`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L547), [`novelty_of_fixedPriorityPhi`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L552), [`sieveOutput`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L564) | `WellFounded.min_mem` |
| **Section 6.1** | Tamari $\mathcal{T}_4$ Catalan cardinality $C_3 = 5$ | [`tamari_le`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L586), [`tamari4_card`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L613) | Finite case exhaustion (`rfl`) |
| **Theorem 6.1** | Constructive bijection $\Phi_{\ge -1}(A_3) \xrightarrow{\sim} \mathrm{Facets}(K_5)$ | [`rootA3_facetK5_equiv`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L670), [`a3_facet_count`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L681) | Constructive two-sided inverse, `interval_cases` |
| **Theorem 7.1** | Positive-definite sum-of-squares Cartan metric | [`cartanForm_sum_of_squares`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L718), [`cartanForm_pos_def`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L730) | `ring`, `nlinarith [sq_nonneg]` |
| **Section 7.2** | Root norm invariance ($=2$), off-diagonal couplings ($-1, 0$) | [`norm_alpha1`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L747), [`strain_adjacent_12`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L754), [`coupled_strain_alpha12`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean#L758) | Bilinear form evaluation (`rfl`) |

### 8.3 Compilation and Machine Verification

- **Formal Target:** [`math_project/MathProject/FunctorialGeometry.lean`](file:///home/shivansh/Github%20Repositories/universe/math_project/MathProject/FunctorialGeometry.lean) (~770 lines of verified code).
- **Environment:** Lean 4 (`v4.33.1`), Mathlib (v4.33.1).
- **Build Command:**
  ```bash
  cd math_project && lake build MathProject.FunctorialGeometry
  ```
  Verified in the Lean 4 kernel with 0 errors and 0 warnings.
- **Axiom Check:** Executing `#print axioms` verifies that all declarations reduce exclusively to the standard core foundations `[propext, Classical.choice, Quot.sound]`.

---

## 9. Conclusion

Formulating partially ordered sets and subobject lattices through category theory creates a clean bridge between order theory, transfinite filtrations, path monoids, and polyhedral root geometry:
1. **Category Structure:** Meets, joins, and closure operators naturally emerge as limits, colimits, and idempotent monads.
2. **Rank Defects:** The submodular defect $\Delta(A, B)$ provides an exact metric measuring deviation from modularity.
3. **Path Valuations:** Quiver traversals evaluate into additive search cost and unipotent shear transport in $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$.
4. **Filtration Limits:** Semi-Artinian objects admit transfinite Loewy reconstructions with vanishing residual colimits.
5. **Polyhedral Duality:** Multi-step composition homotopies assemble into Stasheff associahedra, with $K_5$ boundary facets bijecting to almost-positive roots of $A_3$ under the positive-definite Cartan metric.

---

## References

1. Gabriel, P. (1962). *Des catégories abéliennes.* Bulletin de la Société Mathématique de France, 90, 323-448.
2. Stasheff, J. D. (1963). *Homotopy associativity of H-spaces. I, II.* Trans. Amer. Math. Soc., 108(2), 275-312.
3. Mac Lane, S. (1998). *Categories for the Working Mathematician* (2nd ed.). Springer GTM.
4. Fomin, S., & Zelevinsky, A. (2002). *Cluster algebras I: Foundations.* J. Amer. Math. Soc., 15(2), 497-529.
5. Humphreys, J. E. (1972). *Introduction to Lie Algebras and Representation Theory.* Springer GTM.
6. The mathlib Community. (2020). *The Lean Mathematical Library.* CPP 2020, 367-381.
