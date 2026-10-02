# The Categorical and Geometric Structure of Subobject Lattices

**Author:** Shivansh Singh  
**Date:** March 2026  
**Formalization:** Machine-checked in Lean 4 (Mathlib-compatible, zero `sorry` placeholders, standard core axioms)

---

## Abstract

We study the algebraic, categorical, and geometric structure of partially ordered sets and subobject lattices. By formulating a poset $(L, \le)$ as a thin category, we develop a unified framework spanning three core areas:

1. **Order and Homological Defects:** We realize meets and joins as universal categorical products and coproducts, instantiate closure operators as idempotent categorical monads (`CategoryTheory.Monad`), and characterize submodular rank defects $\Delta(A, B) \ge 0$, showing that $\Delta$ vanishes identically if and only if the rank function is modular.
2. **Filtrations and Path Valuations:** On covering chains, we define a path valuation into the monoid $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$ combining traversal cost with unipotent shear transport, proving functorial concatenation. For semi-Artinian objects in universe-stratified abelian categories ($A : \mathrm{Type}(u+1)$ with $\mathrm{Type}(u)$ morphisms), we construct transfinite cellular filtrations, establish ordinal stabilization at Loewy length $\Omega$, and prove the vanishing of directed residual colimits on the restricted interval category $\mathrm{OrdinalInterval}(\Omega)$.
3. **Polyhedral and Root Geometry:** We analyze morphism compositions through the Tamari lattice $\mathcal{T}_4$ and construct a machine-checked, two-sided constructive equivalence $\mathrm{Root}_{A_n} \simeq \mathrm{Facet}_{K_{n+2}} \simeq \mathrm{Diagonal}(n)$ between almost-positive roots, associahedron facets, and true geometric polygon diagonals. For $n=3$, we prove mechanically that the 9 roots of $A_3$ classify into cyclic length-2 diagonals (6 pentagons) and cyclic length-3 diagonals (3 squares), with all roots sharing invariant norm $\langle v, v \rangle_{A_3} = 2$ under the positive-definite $A_3$ Cartan metric.

All definitions, constructions, and theorems are formally machine-checked in Lean 4 with zero `sorry` placeholders and depend exclusively on standard kernel foundations (`propext`, `Classical.choice`, `Quot.sound`).

---

## 1. Introduction

Partially ordered sets $(L, \le)$ and subobject lattices $\mathrm{Sub}(X)$ are foundational objects across algebra, order theory, and representation theory. While lattices are classically studied through algebraic binary operations $(\wedge, \vee)$, many of their structural features—universal bounds, chain compositions, submodular defects, transfinite filtrations, and higher associativity—are naturally expressed through category theory and geometric combinatorics.

This paper presents a formal categorical and geometric study of subobject lattices, organized around five key components:

1. **Thin Categories and Universal Properties (§2):** We formulate a poset as a thin category $\mathcal{C}_L$, translating order-theoretic meets, joins, and closure operators into categorical products, coproducts, and fully coherent idempotent monads (`CategoryTheory.Monad`).
2. **Submodular Defects and Modularity (§3):** We analyze submodular rank functions $\mathrm{rk} : L \to \mathbb{Z}$ via their defect $\Delta(A, B) = \mathrm{rk}(A) + \mathrm{rk}(B) - \mathrm{rk}(A \vee B) - \mathrm{rk}(A \wedge B)$, proving that non-negativity $\Delta \ge 0$ holds by submodularity and that $\Delta = 0$ characterizes modular rank functions.
3. **Path Valuations on Covering Chains (§4):** We equip covering paths with valuations taking values in the monoid $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$, pairing strictly increasing step costs with upper-triangular unipotent shear transport, and prove homomorphic concatenation.
4. **Transfinite Cellular Filtrations (§5):** In universe-stratified abelian categories ($A : \mathrm{Type}(u+1)$ with $\mathrm{Type}(u)$ morphisms) to avoid Freyd's theorem collapse, we construct transfinite cellular sequences for semi-Artinian objects, proving ordinal stabilization at Loewy length $\Omega$, complete object reconstruction ($C_\Omega = \top$), short exact sequence presentation, and the vanishing of the directed colimit of residual cokernels over the small filtered index category $\mathrm{OrdinalInterval}(\Omega)$.
5. **Associativity Polytopes and $A_n \leftrightarrow K_{n+2}$ Geometric Duality (§6–§7):** We analyze higher parenthesizations through the Stasheff associahedra $K_n$ (including Tamari lattice $\mathcal{T}_4$ of cardinality $C_3 = 5$) and establish a machine-checked two-sided equivalence between almost-positive roots $\Phi_{\ge -1}(A_n)$, boundary facets $\mathrm{Facet}_{K_{n+2}}$, and true polygon diagonals $\mathrm{Diagonal}(n)$, classifying $A_3$ roots into 6 pentagons and 3 squares based on cyclic diagonal length and verifying their norm invariance under the Cartan form.

All definitions, constructions, and theorems in this paper are machine-checked in Lean 4 without `sorry` placeholders.

---

## 2. Posets as Thin Categories

### 2.1 The Categorical Formulation

Let $(L, \le)$ be a partially ordered set. The associated *thin category* $\mathcal{C}_L$ has objects $\mathrm{Ob}(\mathcal{C}_L) = L$ and hom-sets:
$$\mathrm{Hom}_{\mathcal{C}_L}(x, y) = \begin{cases} \{ \ast \} & \text{if } x \le y \\ \varnothing & \text{otherwise} \end{cases}$$

**Proposition 2.1 (Thin Morphism Collapse).**  
*In any thin category $\mathcal{C}_L$:*
1. *Subsingleton Homs:* For all $x, y \in L$, $|\mathrm{Hom}(x, y)| \le 1$.
2. *Monic/Epic Collapse:* Every morphism $f : x \to y$ is simultaneously a monomorphism and an epimorphism.
3. *Endomorphism Rigidity:* The only endomorphism on any object $x$ is the identity: $\mathrm{Hom}(x, x) = \{\mathrm{id}_x\}$.
4. *Trivial Extension Splitting:* Every extension with a retraction splits trivially: if $f : A \to B$ and $p : B \to A$, then $p \circ f = \mathrm{id}_B$ and $f \circ p = \mathrm{id}_A$.

### 2.2 Universal Constructions: Limits and Colimits

When $L$ is a bounded lattice $(L, \wedge, \vee, \bot, \top)$, order operations coincide with categorical limits and colimits:

| Order-Theoretic Notion | Categorical Notion | Universal Characterization |
| :--- | :--- | :--- |
| Bottom Element $\bot$ | Initial Object | Unique morphism $\bot \to x$ for all $x \in L$ |
| Top Element $\top$ | Terminal Object | Unique morphism $x \to \top$ for all $x \in L$ |
| Meet $x \wedge y$ | Categorical Product $x \times y$ | $z \le x \wedge y \iff (z \le x) \wedge (z \le y)$ |
| Join $x \vee y$ | Categorical Coproduct $x \amalg y$ | $x \vee y \le z \iff (x \le z) \wedge (y \le z)$ |
| Infimum $\bigwedge S$ | Small Limit $\varprojlim S$ | Greatest lower bound for diagram $S$ |
| Supremum $\bigvee S$ | Small Colimit $\varinjlim S$ | Least upper bound for diagram $S$ |

### 2.3 Closure Operators and Categorical Monads

A monotone map $F : L \to M$ between posets is canonically a functor $\mathcal{C}_L \to \mathcal{C}_M$.

**Proposition 2.2 (Closure Operators as Categorical Monads).**  
*Let $(L, \le)$ be a poset and let $T : L \to L$ be a closure operator, satisfying:*
1. *Extensivity:* $x \le T(x)$ for all $x \in L$.
2. *Monotonicity:* $x \le y \implies T(x) \le T(y)$.
3. *Idempotency:* $T(T(x)) = T(x)$ for all $x \in L$.

*Then $T$ lifts canonically to an endofunctor $T : \mathcal{C}_L \to \mathcal{C}_L$ and carries the structure of a categorical monad (`CategoryTheory.Monad L`), where:*
- *The unit $\eta : \mathrm{id}_{\mathcal{C}_L} \implies T$ has components $\eta_x = \mathrm{homOfLE}(x \le T(x))$.*
- *The multiplication $\mu : T^2 \implies T$ has components $\mu_x = \mathrm{homOfLE}(T(T(x)) \le T(x))$.*
- *The associativity and unit coherence laws hold automatically by subsingleton hom uniqueness.*

---

## 3. Submodular Rank Defects and Modularity

### 3.1 The Submodular Defect

Let $(L, \wedge, \vee)$ be a lattice. A rank function $\mathrm{rk} : L \to \mathbb{Z}$ is *submodular* if $\mathrm{rk}(A \vee B) + \mathrm{rk}(A \wedge B) \le \mathrm{rk}(A) + \mathrm{rk}(B)$.

**Definition 3.1 (Submodular Defect).** For any pair $A, B \in L$, the submodular defect is:
$$\Delta(A, B) = \big(\mathrm{rk}(A) + \mathrm{rk}(B)\big) - \big(\mathrm{rk}(A \vee B) + \mathrm{rk}(A \wedge B)\big)$$

**Lemma 3.2 (Non-Negativity and Modularity Characterization).**
1. *Non-negativity:* For any submodular rank function, $\Delta(A, B) \ge 0$ for all $A, B \in L$ by definition.
2. *Pairwise Modularity:* $\Delta(A, B) = 0$ if and only if the modular equality holds on $\{A, B\}$:
   $$\mathrm{rk}(A \vee B) + \mathrm{rk}(A \wedge B) = \mathrm{rk}(A) + \mathrm{rk}(B)$$
3. *Modular Rank Functions:* A rank function is modular if and only if $\Delta(A, B) = 0$ identically for all $A, B \in L$.

*Remark 3.3.* A modular rank function should be distinguished from a modular lattice. While any lattice equipped with a strictly monotone modular rank function is modular, the algebraic defect $\Delta$ directly measures the modularity of the valuation itself.

### 3.2 $\mathrm{Tor}_0$ in Thin Categories

In abelian homological algebra, the torsion product $\mathrm{Tor}_0^R(M, N) \cong M \otimes_R N$ measures zero-order algebraic interaction. In thin lattice categories:

**Definition 3.4 ($\mathrm{Tor}_0$ as Categorical Meet).** For $A, B \in L$:
$$\mathrm{Tor}_0(A, B) := A \wedge B$$
This operation is commutative ($A \wedge B = B \wedge A$), associative ($(A \wedge B) \wedge C = A \wedge (B \wedge C)$), and satisfies the universal property $C \le \mathrm{Tor}_0(A, B) \iff (C \le A) \wedge (C \le B)$.

---

## 4. Path Valuations on Covering Quivers

### 4.1 Covering Chains and the Travel Monoid

Let $(L, \le)$ be a locally finite poset. A step $u \lessdot v$ is a *covering relation* (no $z \in L$ satisfies $u < z < v$). A *covering path* is a list $p = [s_1, s_2, \dots, s_k]$ of covering steps.

Let $\mathbf{U}_2(\mathbb{Z})$ denote the multiplicative group of $2 \times 2$ unipotent matrices:
$$\mathbf{U}_2(\mathbb{Z}) = \left\{ \begin{pmatrix} 1 & e \\ 0 & 1 \end{pmatrix} \;\middle|\; e \in \mathbb{Z} \right\}$$
with group multiplication $\begin{pmatrix} 1 & e_1 \\ 0 & 1 \end{pmatrix} \begin{pmatrix} 1 & e_2 \\ 0 & 1 \end{pmatrix} = \begin{pmatrix} 1 & e_1 + e_2 \\ 0 & 1 \end{pmatrix}$.

**Definition 4.1 (Travel Experience Monoid).** The state space is the direct product monoid $\mathcal{M} = (\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$, where elements are pairs $(a, \mathbf{U})$ of accumulated search action $a \in \mathbb{N}$ and parallel transport shear $\mathbf{U} \in \mathbf{U}_2(\mathbb{Z})$, with identity $(0, \mathbf{I})$ and composition:
$$(a_1, \mathbf{U}_1) \star (a_2, \mathbf{U}_2) = (a_1 + a_2, \mathbf{U}_1 \mathbf{U}_2)$$

**Definition 4.2 (Path Valuation).** For a covering step $s = (u \lessdot v)$ with friction cost $c(s) \in \mathbb{N}$ and extension class $e(s) \in \mathbb{Z}$, the step valuation is $\mathbb{T}(s) = (c(s), \begin{pmatrix} 1 & e(s) \\ 0 & 1 \end{pmatrix})$. For a path $p = [s_1, \dots, s_k]$, the path valuation is defined by folding across the step list:
$$\mathbb{T}(p) = \mathrm{pathExperience}(p) \in \mathcal{M}$$

### 4.2 Monoid Laws, Concatenation, and Strict Growth

**Theorem 4.3 (Functorial Path Properties).**
1. *Monoid Associativity and Unitality:* The operation $\star$ on $\mathcal{M}$ is associative with two-sided identity $(0, \mathbf{I})$.
2. *Path Concatenation Homomorphism:* For any two paths $p, q$:
   $$\mathbb{T}(p ++ q) = \mathbb{T}(p) \star \mathbb{T}(q)$$
3. *Strict Action Growth:* For any state $t \in \mathcal{M}$ and any covering step $s = (u \lessdot v)$ with $c(s) > 0$:
   $$\mathrm{Action}(t \star \mathbb{T}(s)) = \mathrm{Action}(t) + c(s) > \mathrm{Action}(t)$$

---

## 5. Transfinite Cellular Filtrations and Basis Discovery

### 5.1 Universe Plumbing and the Loewy Length Theorem

To avoid the collapse of abelian categories with small colimits into trivial preorders (dictated by Freyd's Theorem when objects and morphisms inhabit the same universe), we formulate the ambient abelian category with universe stratification:
$$\mathcal{A} : \mathrm{Type}(u+1), \qquad \mathrm{Hom}_{\mathcal{A}}(X, Y) : \mathrm{Type}(u)$$
equipped with `[Abelian A]`, `[HasLimitsOfSize.{u, u} A]`, `[HasColimitsOfSize.{u, u} A]`, and `[WellPowered.{u} A]`.

An object $U_0 \in \mathcal{A}$ is *semi-Artinian* if for every proper subobject $C < U_0$, the residual quotient $\mathrm{coker}(C \hookrightarrow U_0)$ contains a simple subobject.

**Definition 5.1 (Transfinite Cellular Sequence).** The cellular sequence is constructed transfinitely for ordinals $o \in \mathrm{Ordinal}.\{u\}$:
- **Base Case:** $C_0 = \bot$.
- **Successor Step:** $C_{\alpha+1} = C_\alpha$ if $\mathrm{coker}(C_\alpha \hookrightarrow U_0) = 0$; otherwise, choose a simple subobject $a \hookrightarrow \mathrm{coker}(C_\alpha)$ and pull it back to form $C_{\alpha+1} = \mathrm{pb}(a \to \mathrm{coker}(C_\alpha))$.
- **Limit Ordinal:** $C_\lambda = \sup_{\beta < \lambda} C_\beta$.

**Theorem 5.2 (Cellular Length Existence, Reconstruction, and Colimit Vanishing).**  
*Because the subobject lattice $\mathrm{Sub}(U_0)$ is small (`Small.{u} (Subobject U₀)`), the monotone transfinite sequence $C_\alpha$ must stabilize. Consequently:*
1. *Loewy Length Existence:* There exists an ordinal $\Omega \in \mathrm{Ordinal}.\{u\}$ such that $C_\Omega = \top = U_0$.
2. *Top Reconstruction:* The canonical inclusion morphism $C_\Omega \hookrightarrow U_0$ is an isomorphism.
3. *Cellular Short Exact Sequence:* Every cellular successor step forms a short exact sequence $0 \longrightarrow C_\alpha \longrightarrow C_{\alpha+1} \longrightarrow a \longrightarrow 0$, presenting a length-1 extension.
4. *Vanishing Residual Colimit at Stabilization:* Restricting the transfinite sequence to the small filtered category $\mathrm{OrdinalInterval}(\Omega) := \mathrm{Shrink}.\{u\}(\{b \le \Omega\})$, $\Omega$ is a terminal object where $\mathrm{coker}(C_\Omega \hookrightarrow U_0) \cong 0$. Consequently, the directed colimit of the residual diagram vanishes identically:*
   $$\varinjlim_{j \in \mathrm{OrdinalInterval}(\Omega)} \mathrm{coker}(C_j \hookrightarrow U_0) \cong 0$$

### 5.2 Well-Founded Basis Selection

In a discrete complete lattice $L$ generated by an indexed set $\{e(j) \mid j \in J\}$ under a well-founded priority order $(J, \le)$, the greedy choice function:
$$\phi(x) = \min_{<} \{j \in J \mid e(j) \not\le x\}$$
is well-defined for all $x < \top$. It satisfies the **novelty property**: $e(\phi(x)) \not\le x$, guaranteeing strict progress at every transfinite step toward $\top = \bigvee_{j} e(j)$. The transfinite supremum $\mathrm{sieveOutput} = \sup_{o} x(o)$ formalizes this continuous generator accumulation.

---

## 6. Higher Associativity Polytopes and the $A_n \cong K_{n+2}$ Duality

### 6.1 The Stasheff Associahedra Family

Higher compositions of arrows in category theory assemble into the Stasheff associahedra $K_n$, which correspond to the classical root systems $A_{n-2}$. Under standard Stasheff indexing, $K_n$ is the $(n-2)$-dimensional polytope whose vertices correspond to the $C_{n-1} = \frac{1}{n}\binom{2n-2}{n-1}$ parenthesizations of $n$ composable inputs ($(n-1)$ composable arrows across $n$ objects):

| Polytope | Input Objects | Composable Arrows | Bracketings ($C_{n-1}$) | Dimension | Almost-Positive Roots | Boundary Facets | Categorical Meaning |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **$K_3$** | $3$ ($x_0, x_1, x_2$) | $2$ ($x_0 \xrightarrow{f} x_1 \xrightarrow{g} x_2$) | $C_2 = 2$ | 1D (interval) | $A_1$ ($2$ roots) | $2$ Points | **Binary Associativity** ($h(gf) \leftrightarrow (hg)f$) |
| **$K_4$** | $4$ ($x_0, \dots, x_3$) | $3$ (3 arrows) | $C_3 = 5$ | 2D (pentagon) | $A_2$ ($5$ roots) | $5$ Edges | **Stasheff Pentagon** (Tamari $\mathcal{T}_4$) |
| **$K_5$** | $5$ ($x_0, \dots, x_4$) | $4$ (4 arrows) | $C_4 = 14$ | 3D (polyhedron) | $A_3$ ($9$ roots) | **$9$ Facets (6 Pent + 3 Sq)** | **3D Associahedron** ($K_5 \leftrightarrow A_3$) |
| **$K_6$** | $6$ ($x_0, \dots, x_5$) | $5$ (5 arrows) | $C_5 = 42$ | 4D (polytope) | $A_4$ ($14$ roots) | $14$ Facets | **4D Associahedron** |
| **$K_{n+2}$** | $n+2$ objects | $n+1$ arrows | $C_{n+1}$ | $n$D Polytope | $A_n$ | $\frac{n(n+3)}{2}$ Facets | **Universal Associahedron** |

For $n=4$, the 5 parenthesizations of 4 letters form the vertices of the Tamari lattice $\mathcal{T}_4$ ordered by right-associativity moves, with cardinality exactly $C_3 = 5$.

### 6.2 Universal $N$-Dimensional Associahedron-Root Equivalence ($K_{n+2} \cong A_n$)

For arbitrary rank $n \in \mathbb{N}$, the $(n+2)$-associahedron $K_{n+2}$ corresponds to parenthesizations of $(n+2)$ objects or triangulations of a convex $(n+3)$-gon:
- **Geometric Diagonals $\mathrm{Diagonal}(n)$:** Pairs of vertices $(a, b)$ with $a, b \in \mathrm{Fin}(n+3)$ such that $a + 2 \le b$ and $(a, b) \ne (0, n+2)$.
- **Associahedron Facets $\mathrm{Facet}_{K_{n+2}}$:** Combinatorial representation partitioned into $n$ base chords $\mathrm{base\_diagonal}(k)$ ($0 \le k < n$) and $\frac{n(n+1)}{2}$ internal chords $\mathrm{chord}(i, j)$ ($0 \le i \le j < n$). Total facets: $\binom{n+3}{2} - (n+3) = \frac{n(n+3)}{2}$.
- **Almost-Positive Roots $\Phi_{\ge -1}(A_n)$:** The union of $\frac{n(n+1)}{2}$ positive roots $\alpha_{i..j}$ ($0 \le i \le j < n$) and $n$ negative simple roots $-\alpha_k$ ($0 \le k < n$). Total roots: $\frac{n(n+1)}{2} + n = \frac{n(n+3)}{2}$.

**Theorem 6.1 (Universal Associahedron-Root Equivalence).**  
*For every rank $n \in \mathbb{N}$, there is a machine-checked, two-sided constructive equivalence of types:*
$$\mathrm{Root}_{A_n} \simeq \mathrm{Facet}_{K_{n+2}} \simeq \mathrm{Diagonal}(n)$$
*where:*
1. $\mathrm{Root}_{A_n} \simeq \mathrm{Facet}_{K_{n+2}}$ *is given by $\Xi(\alpha_{i..j}) = \mathrm{chord}(i, j)$ and $\Xi(-\alpha_k) = \mathrm{base\_diagonal}(k)$ with exact two-sided inverse.*
2. $\mathrm{Facet}_{K_{n+2}} \simeq \mathrm{Diagonal}(n)$ *maps combinatorial chords into true polygon diagonals $\mathrm{base\_diagonal}(k) \mapsto (0, k+2)$ and $\mathrm{chord}(i, j) \mapsto (i+1, j+3)$, with proven two-sided inverse `diagonal_to_facetKn2`.*

*Remark 6.2 (Scope of Equivalence).* Theorem 6.1 establishes the precise constructive bijection between almost-positive root generators and polygon boundary diagonals. In the broader Fomin-Zelevinsky cluster algebra framework, these diagonals assemble into triangulations (clusters) via non-crossing compatibility; the formalization in this section specifically establishes the bijective foundation on generators and boundary facets.

### 6.3 Dimension-3 Specialization ($A_3 \leftrightarrow K_5$)

For $n=3$, the 3D associahedron $K_5$ has 14 vertices and exactly **9 boundary facets** (6 pentagonal and 3 square faces).

In Lie theory, the $A_3$ root system contains 6 positive roots $\Phi^+(A_3)$ and 3 negative simple roots $-\Delta(A_3)$, forming the 9 almost-positive roots $\Phi_{\ge -1}(A_3)$:
- **Positive Roots (6):** $\alpha_1, \alpha_2, \alpha_3, \alpha_1+\alpha_2, \alpha_2+\alpha_3, \alpha_1+\alpha_2+\alpha_3$.
- **Negative Simple Roots (3):** $-\alpha_1, -\alpha_2, -\alpha_3$.

The cyclic chord length in a convex 6-gon is $\mathrm{cyclicLength}(a, b) = \min(b - a, 6 - (b - a))$.

**Theorem 6.3 ($A_3 \leftrightarrow K_5$ Cyclic Length Classification).**  
*The equivalence $\mathrm{Root}_{A_3} \simeq \mathrm{Facet}_{K_5}$ maps roots to facets reflecting cyclic diagonal lengths in the hexagon ($n+3 = 6$). Mechanically verified by theorems `rootA3_cyclic_length_pentagon` and `rootA3_cyclic_length_square`:*
- **Pentagons (Cyclic Length 2):**
  - $-\alpha_1 \longleftrightarrow (0, 2)$, $\mathrm{length} = \min(2, 4) = 2$
  - $-\alpha_3 \longleftrightarrow (0, 4)$, $\mathrm{length} = \min(4, 2) = 2$
  - $\alpha_1 \longleftrightarrow (1, 3)$, $\mathrm{length} = \min(2, 4) = 2$
  - $\alpha_2 \longleftrightarrow (2, 4)$, $\mathrm{length} = \min(2, 4) = 2$
  - $\alpha_3 \longleftrightarrow (3, 5)$, $\mathrm{length} = \min(2, 4) = 2$
  - $\alpha_{123} \longleftrightarrow (1, 5)$, $\mathrm{length} = \min(4, 2) = 2$
- **Squares (Cyclic Length 3):**
  - $-\alpha_2 \longleftrightarrow (0, 3)$, $\mathrm{length} = \min(3, 3) = 3$
  - $\alpha_{12} \longleftrightarrow (1, 4)$, $\mathrm{length} = \min(3, 3) = 3$
  - $\alpha_{23} \longleftrightarrow (2, 5)$, $\mathrm{length} = \min(3, 3) = 3$

---

## 7. The $A_n$ Cartan Metric and Quadratic Form

### 7.1 Universal $N$-Dimensional Dirichlet-Cartan Energy

For arbitrary rank $n \in \mathbb{N}$, any vector $v \in \mathbb{Z}^n$ induces an extended vector $\tilde{v} : \{0, 1, \dots, n+1\} \to \mathbb{Z}$ satisfying Dirichlet boundary conditions $\tilde{v}(0) = \tilde{v}(n+1) = 0$. The $A_n$ Cartan quadratic form is given by the discrete Dirichlet energy:
$$Q_n(v) = \sum_{i=0}^n (\tilde{v}(i+1) - \tilde{v}(i))^2$$

**Theorem 7.1 (Universal Positive Definiteness).**  
*For every $n \in \mathbb{N}$ and every $v \in \mathbb{Z}^n$:*
1. *Positive Semi-Definiteness:* $Q_n(v) \ge 0$.
2. *Positive Definiteness:* $Q_n(v) = 0 \iff v = 0$.

### 7.2 Dimension-3 Specialization and Sum-of-Squares

For $n=3$, the Cartan matrix $A_3 = \begin{pmatrix} 2 & -1 & 0 \\ -1 & 2 & -1 \\ 0 & -1 & 2 \end{pmatrix}$ defines the symmetric bilinear form on $\mathbb{Z}^3$:
$$\langle u, v \rangle_{A_3} = 2u_x v_x + 2u_y v_y + 2u_z v_z - (u_x v_y + u_y v_x) - (u_y v_z + u_z v_y)$$

**Theorem 7.2 (Sum-of-Squares Decomposition).**  
*For any vector $v = (x, y, z) \in \mathbb{Z}^3$, the quadratic form decomposes as a sum of four perfect squares:*
$$Q(v) = \langle v, v \rangle_{A_3} = x^2 + (x - y)^2 + (y - z)^2 + z^2$$
*Consequently, $Q(v) \ge 0$ for all $v \in \mathbb{Z}^3$, and $Q(v) = 0 \iff v = 0$.*

### 7.3 Geometric Invariants of the Roots

Under the metric $\langle \cdot, \cdot \rangle_{A_3}$, the roots satisfy exact geometric invariants:
1. **Norm Invariance:** Every root has squared norm exactly $2$ (`rootA3_cartan_norm`):
   $$\langle r, r \rangle_{A_3} = 2 \quad \forall r \in \mathrm{Root}_{A_3}$$
2. **Adjacent Shear Strain:** Adjacent simple roots have inner product $\langle \alpha_1, \alpha_2 \rangle = \langle \alpha_2, \alpha_3 \rangle = -1$.
3. **Orthogonal Decoupling:** Non-adjacent simple roots are orthogonal: $\langle \alpha_1, \alpha_3 \rangle = 0$.
4. **Composite Norm Reconstruction:**
   $$\langle \alpha_1 + \alpha_2, \alpha_1 + \alpha_2 \rangle_{A_3} = \langle \alpha_1, \alpha_1 \rangle + \langle \alpha_2, \alpha_2 \rangle + 2\langle \alpha_1, \alpha_2 \rangle = 2 + 2 - 2 = 2$$

---

## 8. Lean 4 Formalization and Machine Verification

The entirety of the mathematical development presented in Sections 2–7 is formalized in Lean 4 as the standalone module [`FunctorialGeometry.lean`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean) within the `MathProject` workspace.

### 8.1 Design Principles and Axiomatic Foundations

The formal development follows three structural principles:
1. **Categorical Integration with Mathlib:** Rather than using ad-hoc posetal order structures, thin categories and subobject lattices are expressed directly through Mathlib's native category theory library (`CategoryTheory.Subobject`, `CategoryTheory.Abelian`, `CategoryTheory.Monad`, and `CategoryTheory.Limits`).
2. **Constructive Computational Core:** Discrete and algebraic structures—including the travel monoid $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$, the Tamari poset $\mathcal{T}_4$, the general $A_n \leftrightarrow K_{n+2}$ equivalence, the polygon diagonal mapping $\mathrm{Diagonal}(n)$, the $A_3 \leftrightarrow K_5$ root-facet bijection, and the Cartan quadratic forms—are defined constructively with `DecidableEq` instances and verified by computation (`rfl`, `decide`, `ring`, `omega`).
3. **Classical Homological Framework:** Abstract abelian categories and transfinite ordinals use standard classical logic (`Classical.choice`, `open Classical`) for subobject selection and non-constructive colimits (Theorem 5.2).

The `#print axioms` command confirms that all declarations compile without `sorry` placeholders and depend exclusively on Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

### 8.2 Paper-to-Code Correspondence Matrix

| Paper Statement | Mathematical Concept | Lean 4 Declaration | Proof Technique / Tactic |
| :--- | :--- | :--- | :--- |
| **Proposition 2.1** | Subsingleton homs, monic/epic collapse, split extensions | [`thin_mono`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L70), [`thin_epi`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L76), [`thin_extension_splits`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L86) | `Subsingleton.elim` |
| **Section 2.2** | Meets as categorical products, joins as coproducts | [`meet_universal`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L130), [`join_universal`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L138), [`subobject_mono`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L152) | `le_inf`, `sup_le`, `inferInstance` |
| **Proposition 2.2** | Closure operators as idempotent monads | [`ClosureOperator`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L106), [`ClosureOperator.toMonad`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L119) | `CategoryTheory.Monad`, `thin_hom_unique` |
| **Lemma 3.2** | Submodular defect $\Delta \ge 0$, modularity criterion $\Delta = 0$ | [`submodularDefect`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L175), [`defect_nonneg`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L179), [`defect_zero_iff_modular`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L186) | `linarith` |
| **Section 3.2** | $\mathrm{Tor}_0$ realized as categorical meet | [`tor0`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L201), [`tor0_comm`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L203), [`tor0_universal`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L209) | Infimum symmetry and universal properties |
| **Theorem 4.3** | Travel monoid laws, path concatenation, strict growth | [`Unipotent2`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L223), [`TravelExperience`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L254), [`pathExperience_append`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L306), [`action_strictly_increases`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L313) | Upper-triangular matrix arithmetic, `linarith` |
| **Theorem 5.2 (1–2)** | Loewy length existence $\Omega$, stabilization, top reconstruction | [`loewySequence_mono`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L470), [`loewy_length_exists`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L500), [`reconstruction`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L512), [`reconstruction_iso`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L516) | `Ordinal.limitRecOn`, `eventuallyConst`, `Subobject.top_arrow_isIso` |
| **Theorem 5.2 (3)** | Cellular Short Exact Sequence | [`cellularShortComplex`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L653), [`cellular_shortExact`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L723) | `ShortComplex.exact_of_f_is_kernel`, `pullback` |
| **Theorem 5.2 (4)** | Vanishing residual colimit over $\mathrm{OrdinalInterval}$ | [`loewyIntervalFunctor`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L597), [`loewy_residual_colimit_vanishes`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L604) | Filtered colimit absorption, `isZero_cokernel_of_epi` |
| **Section 5.2** | Well-founded basis selection and novelty property | [`candidates_nonempty`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L736), [`fixedPriorityPhi`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L748), [`novelty_of_fixedPriorityPhi`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L753), [`sieveOutput`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L765) | `WellFounded.min_mem` |
| **Section 6.1** | Tamari $\mathcal{T}_4$ Catalan cardinality $C_3 = 5$ | [`tamari_le`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L787), [`tamari4_card`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L814) | Finite case exhaustion (`rfl`) |
| **Theorem 6.1** | Two-sided geometric equivalence $\mathrm{Root}_{A_n} \simeq \mathrm{Facet}_{K_{n+2}} \simeq \mathrm{Diagonal}(n)$ | [`facetKn2_diagonal_equiv`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L881), [`rootAn_facetKn2_equiv`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L902), [`rootAn_diagonal_equiv`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L910) | `Fin.isLt`, `omega`, two-sided inverse proofs |
| **Theorem 6.3** | Constructive bijection $\Phi_{\ge -1}(A_3) \simeq \mathrm{Facets}(K_5)$ & Cyclic Length Theorems | [`rootA3_facetK5_equiv`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L980), [`rootA3_cyclic_length_pentagon`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L987), [`rootA3_cyclic_length_square`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L991) | Constructive two-sided inverse, `cases`, `rfl` |
| **Theorem 7.1** | Universal positive-definite $A_n$ Dirichlet-Cartan metric | [`cartanEnergy_nonneg`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L1021), [`cartanEnergy_pos_def`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L1027) | `Finset.sum_eq_zero_iff_of_nonneg`, induction, `omega` |
| **Section 7.2** | Sum-of-squares $A_3$ Cartan metric | [`cartanForm_sum_of_squares`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L1092), [`cartanForm_pos_def`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L1103) | `ring`, `nlinarith [sq_nonneg]` |
| **Section 7.3** | Root norm invariance ($=2$), off-diagonal couplings ($-1, 0$) | [`norm_alpha1`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L1122), [`rootA3_cartan_norm`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L1146), [`strain_adjacent_12`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L1129), [`coupled_strain_alpha12`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean#L1133) | Bilinear form evaluation (`rfl`) |

### 8.3 Compilation and Machine Verification

- **Formal Target:** [`math_project/MathProject/FunctorialGeometry.lean`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/MathProject/FunctorialGeometry.lean) (~1270 lines of code).
- **Environment:** Lean 4 (`leanprover/lean4:v4.33.1`), Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` (pinned in [`lake-manifest.json`](https://raw.githubusercontent.com/sh7vansh/universe/main/math_project/lake-manifest.json)).
- **Build Command:**
  ```bash
  cd math_project && lake build MathProject.FunctorialGeometry
  ```
  Compiles with 0 kernel errors.
- **Axiom Check:** Executing `#print axioms` verifies that all declarations reduce exclusively to the standard core foundations `[propext, Classical.choice, Quot.sound]`.


## 9. Conclusion

We have established a categorical and geometric framework for partially ordered sets and subobject lattices:
1. **Category Structure:** Meets, joins, and closure operators emerge as limits, colimits, and idempotent monads (`CategoryTheory.Monad`).
2. **Defect Theory:** Modularity of valuations is governed by the non-negative defect $\Delta \ge 0$, whose vanishing characterizes modular rank functions.
3. **Monoidal Dynamics:** Path valuations into $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$ capture traversal friction and shear transport with homomorphic path concatenation.
4. **Filtration Limits:** Semi-Artinian objects in universe-stratified abelian categories admit transfinite Loewy reconstructions with vanishing residual colimits over restricted ordinal intervals at stabilization.
5. **Polyhedral Duality:** Multi-step composition homotopies assemble into Stasheff associahedra, with boundary facets and $A_n$ almost-positive roots equivalent to true geometric polygon diagonals, and $A_3$ roots classified mechanically by cyclic length into 6 pentagons and 3 squares under the positive-definite Cartan metric.

All results compile in Lean 4 without `sorry` placeholders and depend solely on standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## References

1. Stasheff, J. D. (1963). *Homotopy associativity of $H$-spaces. I, II.* Trans. Amer. Math. Soc., 108:275–312.
2. Mac Lane, S. (1998). *Categories for the Working Mathematician.* Springer Graduate Texts in Mathematics, 2nd ed.
3. Fomin, S., & Zelevinsky, A. (2003). *$Y$-systems and generalized associahedra.* Ann. of Math. (2), 158(3):977–1018.
4. Freyd, P. (1964). *Abelian Categories: An Introduction to the Theory of Functors.* Harper & Row.
5. The mathlib Community. (2020). *The Lean Mathematical Library.* In Proc. CPP 2020, pages 367–381.
