# The Categorical and Geometric Structure of Subobject Lattices

**Author:** Shivansh Singh<br>
**Date:** March 2026<br>
**Formalization:** Machine-checked in Lean 4 (Mathlib-compatible, zero `sorry` placeholders, standard core axioms)

---

## Abstract

The main question is how the thin category of a poset relates to the associahedra. For a chain of $n$ arrows, all full bracket patterns give the same composite arrow. If we retain the bracket patterns, their partial-bracketing order is isomorphic to the order of noncrossing diagonal sets in an $(n+1)$-gon. We prove this order isomorphism for every arity in Lean. We then construct Loday's convex hull and prove its supporting-face order, tree-to-vertex correspondence, affine dimension, and vertex and facet counts for every $n \ge 2$. The nullary and unary cases use explicit conventions.

We study the algebraic, categorical, and geometric structure of partially ordered sets and subobject lattices. By formulating a poset $(L, \le)$ as a thin category, we develop a unified formal framework spanning three core areas:

1. **Order and Submodular Defects:** We realize meets and joins as universal categorical products and coproducts, instantiate closure operators as idempotent categorical monads (`CategoryTheory.Monad`), and characterize submodular defects $\Delta(A, B) \ge 0$, showing that $\Delta$ vanishes identically if and only if the rank valuation is modular. We define the meet interaction $A \sqcap B$.
2. **Polyhedral and Root Geometry:** We analyze higher associativity through the Tamari lattice $\mathcal{T}_4$ and formalize a bijection in the fan-triangulation model via a machine-checked, two-sided constructive equivalence $\mathrm{Root}_{A_n} \simeq \mathrm{Facet}_{K_{n+2}} \simeq \mathrm{Diagonal}(n)$ between almost-positive roots, Stasheff associahedron facets, and geometric polygon diagonals. For $n=3$, we prove mechanically that the 9 roots of $A_3$ classify into cyclic length-2 diagonals (6 pentagons) and cyclic length-3 diagonals (3 squares), where every almost-positive root has norm $\langle v, v \rangle_{A_3} = 2$ under the discrete Dirichlet–Cartan quadratic form on $\mathbb{Z}^3$.
3. **Path Valuations and Chain Applications:** On directed step sequences (representing covering chains in discrete quivers), we define a path valuation into the product monoid $(\mathbb{N}, +) \times (\mathbb{Z}, +)$ tracking accumulated cost alongside integer shear labels, proving functorial path concatenation. For each fixed labelled chain, all full bracket patterns give the same arrow and the same valuation. As an application, for semi-Artinian objects in universe-stratified abelian categories ($\mathcal{A} : \mathrm{Type}(u+1)$ with $\mathrm{Type}(u)$ morphisms), we construct a one-simple-at-a-time transfinite filtration, a transfinite composition series, establish ordinal stabilization at cellular length $\Omega$, and prove the vanishing of directed residual colimits on the restricted interval category $\mathrm{OrdinalInterval}(\Omega)$.

The Lean results listed in Section 8 are machine-checked with zero `sorry` placeholders and use only standard core axioms (`propext`, `Classical.choice`, `Quot.sound`). The general convex realization and its geometric counts are included in these proofs.

---

## 1. Introduction

Partially ordered sets $(L, \le)$ and subobject lattices $\mathrm{Sub}(X)$ are foundational objects across algebra, order theory, and representation theory. While lattices are classically studied through algebraic binary operations $(\wedge, \vee)$, many of their structural features—universal bounds, chain compositions, submodular defects, transfinite filtrations, and higher associativity—are naturally expressed through category theory and geometric combinatorics.

This paper presents a formal categorical and geometric study of subobject lattices, structured across three major mathematical stages:

- **Stage I: Categorical Foundations & Submodular Defects (Part I, §§2–3):**
  We formulate posets as thin categories $\mathcal{C}_L$, translating meets and joins into universal categorical products and coproducts, and closure operators into fully coherent idempotent monads (`CategoryTheory.Monad`). We analyze submodular rank functions $\mathrm{rk} : L \to \mathbb{Z}$ via their defect $\Delta(A, B) = \mathrm{rk}(A) + \mathrm{rk}(B) - \mathrm{rk}(A \vee B) - \mathrm{rk}(A \wedge B)$, showing non-negativity $\Delta \ge 0$ characterizes submodularity and $\Delta \equiv 0$ characterizes modular valuations.

- **Stage II: Associahedra, Higher Associativity & Root Geometry (Part II, §§4–5):**
  We formalize the Stasheff associahedra $K_{n+2}$ and establish a machine-checked, two-sided constructive equivalence $\mathrm{Root}_{A_n} \simeq \mathrm{Facet}_{K_{n+2}} \simeq \mathrm{Diagonal}(n)$ between almost-positive roots, associahedron facets, and polygon diagonals. For $n=3$, we mechanically classify roots into 6 pentagons and 3 squares by cyclic chord length. Finally, we formalize the $A_n$ Cartan form as a discrete 1D Dirichlet energy on $\mathbb{Z}^n$ with Dirichlet boundary conditions, proving positive definiteness and intrinsic norm invariance $\langle v, v \rangle = 2$.

- **Stage III: Path Valuations & Chain Applications (Part III, §§6–7):**
  On covering quivers, we define functorial path valuations into the monoid $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$ tracking path cost alongside integer shear labels. We prove that all full bracket patterns of a fixed labelled chain give the same arrow and the same valuation. As an application, in universe-stratified abelian categories ($\mathcal{A} : \mathrm{Type}(u+1)$ with $\mathrm{Type}(u)$ morphisms, avoiding Freyd's size collapse), we build fine transfinite cellular filtrations for semi-Artinian objects attaching single simple cells via short exact sequences $0 \to C_\alpha \to C_{\alpha+1} \to a \to 0$. We prove ordinal stabilization at length $\Omega$, top reconstruction $C_\Omega = \top$, and vanishing residual cokernel colimits over $\mathrm{OrdinalInterval}(\Omega)$.

The formal results are checked in Lean 4 without `sorry` placeholders. The bracket, polygon, and convex supporting-face models are connected by proved order isomorphisms.

---

# Part I: Categorical Foundations and Submodular Defects

## 2. Posets as Thin Categories

### 2.1 The Categorical Formulation

A partially ordered set $(L, \le)$ canonically defines a small category $\mathcal{C}_L$ where:
- $\mathrm{Ob}(\mathcal{C}_L) = L$.
- For any $x, y \in L$, $\mathrm{Hom}_{\mathcal{C}_L}(x, y) = \{*\}$ if $x \le y$, and $\emptyset$ otherwise.

**Proposition 2.1 (Thinness and Monic/Epic Collapse).** *In any thin category:*

1. *Subsingleton Hom-Sets:* For all $x, y \in L$, $\mathrm{Hom}(x, y)$ is a subsingleton (`Subsingleton (x ⟶ y)`).
2. *Monic/Epic Collapse:* Every morphism $f : x \to y$ is simultaneously a monomorphism (`Mono f`) and an epimorphism (`Epi f`).
3. *Endomorphism Identity:* Any endomorphism $f : x \to x$ equals $\mathbb{1}_x$.
4. *Split Retraction:* Any extension with a retraction splits trivially: if $f : A \to B$ and $p : B \to A$, then $p \circ f = \mathbb{1}_A$ and $f \circ p = \mathbb{1}_B$.

*Proof.* In Lean 4, parallel morphisms $g, h : z \to x$ are identical by `Subsingleton.elim g h`. Thus $f \circ g = f \circ h \implies g = h$ trivially, establishing `Mono f` and `Epi f`. Split extensions follow by uniqueness of endomorphisms. $\blacksquare$

### 2.2 Universal Constructions: Limits and Colimits

In a lattice $(L, \wedge, \vee)$, meets and joins satisfy universal categorical limit and colimit properties:
- **Meets as Products:** The infimum $x \wedge y$ satisfies $x \wedge y \le x$, $x \wedge y \le y$, and $(z \le x \text{ and } z \le y) \implies z \le x \wedge y$. In $\mathcal{C}_L$, $x \wedge y$ is the categorical product $x \times y$.
- **Joins as Coproducts:** The supremum $x \vee y$ satisfies $x \le x \vee y$, $y \le x \vee y$, and $(x \le z \text{ and } y \le z) \implies x \vee y \le z$. In $\mathcal{C}_L$, $x \vee y$ is the categorical coproduct $x \amalg y$.

For any object $X$ in a category $\mathcal{C}$, the subobject lattice $\mathrm{Sub}(X)$ forms a thin category where meets and joins represent intersections and sums of subobjects.

### 2.3 Closure Operators and Categorical Monads

A *closure operator* on $(L, \le)$ is a map $\mathrm{cl} : L \to L$ satisfying:

1. **Extensive:** $x \le \mathrm{cl}(x)$ for all $x \in L$.
2. **Monotone:** $x \le y \implies \mathrm{cl}(x) \le \mathrm{cl}(y)$.
3. **Idempotent:** $\mathrm{cl}(\mathrm{cl}(x)) = \mathrm{cl}(x)$ for all $x \in L$.

**Proposition 2.2 (Closure Operators as Idempotent Monads).** *A closure operator $\mathrm{cl} : L \to L$ canonically defines an idempotent monad $(T, \eta, \mu)$ on the thin category $\mathcal{C}_L$ (`CategoryTheory.Monad`), where:*
- *Functor:* $T(x) = \mathrm{cl}(x)$, with morphism mapping $T(f) = \mathrm{homOfLE}(\mathrm{cl}(x \le y))$.
- *Unit:* $\eta_x : x \to T(x)$ is the unique morphism $\mathrm{homOfLE}(x \le \mathrm{cl}(x))$.
- *Multiplication:* $\mu_x : T^2(x) \to T(x)$ is the unique morphism $\mathrm{homOfLE}(\mathrm{cl}(\mathrm{cl}(x)) \le \mathrm{cl}(x))$.

*Proof.* Monad associativity $\mu \circ T\mu = \mu \circ \mu T$ and unit laws $\mu \circ \eta T = \mathbb{1} = \mu \circ T\eta$ hold automatically by subsingleton hom-set uniqueness (`Subsingleton.elim`). $\blacksquare$

**Lemma 2.3 (Galois Connections Induce Closure Monads).** *Any Galois connection (adjunction) $l \dashv u$ between posets $L$ and $M$ induces an idempotent closure operator $\mathrm{cl} = u \circ l$ on $L$, and hence an idempotent monad on $\mathcal{C}_L$.*

---

## 3. Submodular Defects and Modularity

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

### 3.2 Meet Interaction in Thin Categories

We define the meet interaction $A \wedge B$.

**Definition 3.4 (Meet Interaction).** For $A, B \in L$:
$$\mathrm{meetInteraction}(A, B) := A \wedge B$$
This operation is commutative ($A \wedge B = B \wedge A$), associative ($(A \wedge B) \wedge C = A \wedge (B \wedge C)$), and satisfies the universal property $C \le \mathrm{meetInteraction}(A, B) \iff (C \le A) \text{ and } (C \le B)$.

The submodular defect $\Delta(A, B)$ measures failure of modular additivity of valuations across meets and joins.

---

# Part II: Higher Associativity, Associahedra, and Root Geometry

This part uses the thin-category result from §2. A finite chain has one composite arrow. Its retained bracket patterns define the associahedral face order. We then construct the convex realization and study its root labels.

## 4. Higher Associativity Polytopes and Type $A_n$ Root Labels

### 4.1 The Stasheff Associahedra Family

For $n \ge 2$, the Stasheff associahedron $K_n$ has dimension $n-2$. Its vertices correspond to the $C_{n-1} = \frac{1}{n}\binom{2n-2}{n-1}$ full bracket patterns of $n$ inputs. A chain of $n$ arrows supplies these inputs. Thinness makes their composite arrow unique. The bracket patterns supply the associahedral structure.

**Theorem 4.0 (Bracket-to-Face Order for Every Arity).** Let $L$ be a poset and let $x_0 \le \cdots \le x_n$ be a chain. For $n \ge 2$, define:

- $P_n$: finite sets of proper bracket intervals $[a,b)$, with $0 \le a$, $a+2 \le b \le n$, and $(a,b) \ne (0,n)$. Each pair of intervals must be disjoint or nested.
- $F_n$: finite sets of polygon diagonals $(a,b)$ on vertices $0,\ldots,n$. No two diagonal interiors may cross.

Order both sets by reverse inclusion. Then the map $[a,b) \mapsto (a,b)$ gives an order isomorphism:
$$P_n \simeq_o F_n.$$
The empty diagonal set denotes the whole face. It does not denote the empty face. Thus $F_n$ is the standard combinatorial model of the **nonempty** faces of $K_n$.

*Proof.* Two intervals are disjoint or nested if and only if their endpoints do not strictly interleave. Strict interleaving is exactly the crossing condition for polygon diagonals. The endpoint map and its inverse therefore preserve compatible sets. They also preserve inclusion and reverse inclusion. In Lean, `bracketCompatible_iff_noncrossing` proves the compatibility step, and `partialBracketing_face_orderIso` proves the order isomorphism.

Set `KnBracketing 0 = KnFace 0 = Empty`. At arity one, use the single pattern with no brackets. With these explicit conventions, `all_Kn_orderIso` applies to every $n : \mathbb{N}$, and `all_Kn_categoryEquivalence` identifies the corresponding thin categories. The unary member is a unit point; the dimension formula applies only for $n \ge 2$.

For the given finite chain, `evalChainBracketing` evaluates a binary tree by categorical composition. The theorem `all_Kn_chain_composites` proves that any two full bracket patterns give the same arrow $x_0 \to x_n$. The theorem `all_Kn_thin_composition` combines this result with the face-order isomorphism. A nullary composite is the identity arrow (`evalNullary`); it is separate from the empty member $K_0$.

For every $m \ge 0$, the general count is also proved:
$$\#\mathrm{FullBracketing}(m+1)=C_m=\frac{1}{m+1}\binom{2m}{m}.$$
The declarations are `fullBracketing_card` and `fullBracketing_card_formula`. The theorem `fullBracketing_vertex_equiv` now identifies full binary trees with the minimal polygon faces. Its proof completes each compatible interval family to a tree, proves that the interval family determines the tree, and proves maximality from the group-count bound.

**Theorem 4.0.1 (Convex Realization, Dimension, and Counts).** For every $r \ge 0$, let $Q_r$ be the convex hull of the binary-tree points in $\mathbb{R}^{r+1}$. At each internal tree split, the gap coordinate is the number of leaves in the left child times the number in the right child. Then:

1. $Q_r$ is nonempty, compact, and convex (`LodayPolytope_nonempty`, `LodayPolytope_compact`, `LodayPolytope_convex`).
2. Its nonempty supporting-face order is isomorphic to $F_{r+2}$ (`polygon_loday_face_orderIso`). A supporting face is the set where a linear functional has its minimum on $Q_r$.
3. Its extreme points are exactly the binary-tree points (`LodayPolytope_extremePoints`). Distinct trees give distinct points (`lodayPoint_injective`).
4. Its actual affine dimension is $r$ (`Loday_affine_dimension`). This is the finite rank of the direction of its affine span, not a dimension assigned by definition.
5. Its geometric vertex count is $C_{r+1}$ (`Loday_geometric_vertex_count`).
6. Its geometric facet count is $r(r+3)/2$ (`Loday_geometric_facet_count`). Here a facet is a maximal proper member of the supporting-face order.

Thus, with $n=r+2$:
$$\dim K_n=n-2,\qquad
\#\operatorname{Vert}(K_n)=\frac{1}{n}\binom{2n-2}{n-1},\qquad
\#\operatorname{Facet}(K_n)=\frac{(n+1)(n-2)}{2}.$$

*Proof.* Each interval sum is at least the triangle number for its leaf count. Equality holds exactly for a subtree interval (`treeIntervalSum_eq_iff`). These equalities determine the coordinates uniquely. They prove that each tree point is extreme; the finite convex hull has no other extreme points. Every linear functional has an interval certificate on a tree, with nonnegative coefficients on proper intervals (`tree_normal_certificate`). This proves that each supporting face is a bracket face. A tree rotation removes any group absent from a partial pattern while retaining its other groups, so the face map also reflects the order. Strict supporting-face chains give the affine-dimension lower bound. The fixed total coordinate sum gives the upper bound. The tree and diagonal bijections give the counts. All these steps are checked in Lean.

The theorem `all_Kn_poset_realization` combines the convex realization and counts with equality of the composite arrows for any poset chain. The map `all_Kn_geometric_orderIso` includes $K_0$ and $K_1$ under the stated conventions. Loday's construction is described in [Realization of the Stasheff polytope](https://arxiv.org/abs/math/0212126).

**Theorem 4.0.2 (Facet Product Face Order).** Let $d=(a,b)$ be a diagonal of the $(n+1)$-gon for $K_n$. Put $m=b-a$ and $k=n+1-m$. Then $m,k\ge2$, and the nonempty subfaces of the facet indexed by $d$ have the product order
$$\{G : G\text{ is a nonempty face of }K_n,\ G\le F_d\}\simeq_o
\operatorname{Faces}_{\ne\emptyset}(K_m)\times\operatorname{Faces}_{\ne\emptyset}(K_k).$$
The declarations `polygonFacet_product_orderIso` and `Loday_facet_geometric_product_orderIso` prove this for the polygon model and the actual convex supporting-face model. This specifies the combinatorial type; it does not assert metric regularity.

*Proof.* The diagonal splits the polygon into one polygon with vertices $a,\ldots,b$ and a complementary polygon. Every other diagonal that does not cross $d$ belongs to exactly one side. The endpoint maps preserve crossings within a side, and diagonals on different sides do not cross. A face containing $d$ therefore splits into a pair of compatible diagonal sets. Conversely, insert $d$ and unite the two embedded sets. These maps preserve reverse inclusion and give the order isomorphism. Restrict the proved polygon-to-convex face map to the subfaces of the facet, then apply the same face map to both smaller factors.

| Member | Chain positions | Composable arrows | Full binary bracketings | Dimension | Almost-positive root labels | Boundary facets | Categorical Meaning |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **$K_0$** | $1$ ($x_0$) | $0$ (nullary) | $0$ binary trees | Not assigned; empty by convention | — | $0$ | **Empty nullary member**; empty composition is $\mathbb{1}_{x_0}$ |
| **$K_1$** | $2$ ($x_0, x_1$) | $1$ ($x_0 \xrightarrow{f} x_1$) | $C_0 = 1$ | 0D point, by convention | — | $0$ | **Unary evaluation** gives $f$ |
| **$K_2$** | $3$ ($x_0, x_1, x_2$) | $2$ ($x_0 \xrightarrow{f} x_1 \xrightarrow{g} x_2$) | $C_1 = 1$ | 0D (point) | $A_0$ ($0$ roots) | $0$ | **Binary Composition** ($(gf)$) |
| **$K_3$** | $4$ ($x_0, \dots, x_3$) | $3$ ($x_0 \xrightarrow{f} x_1 \xrightarrow{g} x_2 \xrightarrow{h} x_3$) | $C_2 = 2$ | 1D (interval) | $A_1$ ($2$ roots) | $2$ Points | **Ternary Associativity** ($h(gf) \leftrightarrow (hg)f$) |
| **$K_4$** | $5$ ($x_0, \dots, x_4$) | $4$ (4 arrows) | $C_3 = 5$ | 2D (pentagon) | $A_2$ ($5$ roots) | $5$ Edges | **Stasheff Pentagon** (Tamari $\mathcal{T}_4$) |
| **$K_5$** | $6$ ($x_0, \dots, x_5$) | $5$ (5 arrows) | $C_4 = 14$ | 3D (polyhedron) | $A_3$ ($9$ roots) | **9 facets: 6 pentagons and 3 squares** | **3D Associahedron** ($K_5 \leftrightarrow A_3$) |
| **$K_6$** | $7$ ($x_0, \dots, x_6$) | $6$ (6 arrows) | $C_5 = 42$ | 4D (polytope) | $A_4$ ($14$ roots) | $14$ Facets | **4D Associahedron** |
| **$K_{n+2}$** | $n+3$ objects | $n+2$ arrows | $C_{n+1}$ | $n$-dimensional | $A_n$ ($\frac{n(n+3)}{2}$ roots) | $\frac{n(n+3)}{2}$ Facets | **Higher $n$-Associativity** |

Chain positions can contain repeated objects. The Catalan formula $C_{n-1}$ for full binary bracketings applies for $n \ge 1$. At $n=0$, the empty categorical composition is defined separately from full binary trees. The Tamari order is an order on full bracketings; the face order uses compatible partial bracket patterns and reverse inclusion. Facet shape names describe combinatorial type, without an assertion of equal side lengths or angles.

In Lean 4, parenthesizations for $K_2$ (`Tree2`, $C_1 = 1$), $K_3$ (`Tree3`, $C_2 = 2$), and $K_4$ (`Tree4`, $C_3 = 5$) are formalized constructively, with Catalan cardinalities machine-checked (`tamari2_card`, `tamari3_card`, `tamari4_card`).

### 4.2 Almost-Positive Roots and Associahedron Facets for Every Rank

A celebrated result in algebraic combinatorics (Fomin–Zelevinsky, 2003; Lee, 1989) establishes that the boundary facets of the Stasheff associahedron $K_{n+2}$ are in bijection with the almost-positive roots of type $A_n$, $\Phi_{\ge -1}(A_n)$, and with the internal diagonals of a regular $(n+3)$-gon.

In `FunctorialGeometry.lean`, we formalize a bijection in the fan-triangulation model constructively for arbitrary rank $n \in \mathbb{N}$:
- **Almost-Positive Roots ($\mathrm{Root}_{A_n}$):** Comprises $\binom{n+1}{2} = \frac{n(n+1)}{2}$ positive roots $\alpha_{i..j}$ ($0 \le i \le j < n$) and $n$ negative simple roots $-\alpha_k$ ($0 \le k < n$), totaling $\frac{n(n+3)}{2}$ roots.
- **Associahedron Facets ($\mathrm{Facet}_{K_{n+2}}$):** Partitioned into $n$ base diagonals and $\frac{n(n+1)}{2}$ internal chords.
- **Polygon Diagonals ($\mathrm{Diagonal}(n)$):** Pairs of vertices $(a, b)$ of an $(n+3)$-gon with $a + 2 \le b$ and $(a, b) \ne (0, n+2)$.

**Theorem 4.1 (Explicit Indexing Bijection).**
*For every $n \in \mathbb{N}$, there exist explicit constructive bijections with machine-checked two-sided inverses:*
$$\mathrm{Root}_{A_n} \xrightarrow[\sim]{\mathrm{rootAn\_facetKn2\_equiv}} \mathrm{Facet}_{K_{n+2}} \xrightarrow[\sim]{\mathrm{facetKn2\_diagonal\_equiv}} \mathrm{Diagonal}(n)$$
*Their composition yields the universal root-diagonal equivalence $\mathrm{Root}_{A_n} \simeq \mathrm{Diagonal}(n)$ (`rootAn_diagonal_equiv`).*

The declaration `diagonal_polygon_equiv` identifies this diagonal type with the general polygon face model. Composing with the proved diagonal-to-convex-facet equivalence gives `rootAn_lodayFacet_equiv`, an equivalence between the root labels and the actual supporting facets of the convex realization.

**Definition 4.2 (Cyclic Length).** For any diagonal $d = (a, b)$ of an $(n+3)$-gon, its cyclic length is:
$$\ell_{\mathrm{cyc}}(d) = \min\big(b - a, \, (n + 3) - (b - a)\big)$$

### 4.3 Dimension-3 Specialization ($A_3 \leftrightarrow K_5$)

For $n=3$, the associahedron $K_5$ is a 3-dimensional polyhedron with 14 vertices (the Catalan number $C_4 = 14$ binary bracketings of 5 letters) and $9$ boundary facets ($\frac{3 \times 6}{2} = 9$ facets). The almost-positive root system of $A_3$ contains $9$ roots:
- $6$ positive roots: $\alpha_1, \alpha_2, \alpha_3, \alpha_{12}, \alpha_{23}, \alpha_{123}$.
- $3$ negative simple roots: $-\alpha_1, -\alpha_2, -\alpha_3$.

**Theorem 4.3 (A₃ Root Classification by Cyclic Length).**
*The constructive bijection `rootA3_facetK5_equiv` assigns pentagon/square labels to the 9 roots and checks them against their cyclic length:*

1. *Pentagonal Facets (6 Roots):* The 6 roots $\{-\alpha_1, -\alpha_3, \alpha_1, \alpha_2, \alpha_3, \alpha_{123}\}$ map to chords of cyclic length $2$ (`rootA3_cyclic_length_pentagon`), corresponding to pentagonal boundary faces of $K_5$.
2. *Square Facets (3 Roots):* The 3 roots $\{-\alpha_2, \alpha_{12}, \alpha_{23}\}$ map to chords of cyclic length $3$ (`rootA3_cyclic_length_square`), corresponding to square boundary faces of $K_5$.

The facet shapes now follow from Theorem 4.0.2. A cyclic length-2 diagonal splits the hexagon into a triangle and a pentagon, so its facet has type $K_2\times K_4\cong K_4$. A cyclic length-3 diagonal splits it into two quadrilaterals, so its facet has type $K_3\times K_3$, a square. The symbol $\cong$ here denotes combinatorial type. The Lean theorems `Loday_K5_pentagonal_facet` and `Loday_K5_square_facet` identify the actual supporting-face orders. The theorems `rootA3_geometric_pentagonal_facet` and `rootA3_geometric_square_facet` connect these shapes to the existing root labels. The actual facet counts are six and three (`Loday_K5_pentagonal_facet_count`, `Loday_K5_square_facet_count`).

---

## 5. The $A_n$ Cartan Metric and Quadratic Form

### 5.1 Universal $N$-Dimensional Dirichlet-Cartan Energy

For arbitrary rank $n \in \mathbb{N}$, any vector $v \in \mathbb{Z}^n$ induces an extended vector $\tilde{v} : \{0, 1, \dots, n+1\} \to \mathbb{Z}$ satisfying Dirichlet boundary conditions $\tilde{v}(0) = \tilde{v}(n+1) = 0$. The $A_n$ Cartan quadratic form is given by the discrete Dirichlet energy:
$$Q_n(v) = \sum_{i=0}^n (\tilde{v}(i+1) - \tilde{v}(i))^2$$

**Theorem 5.1 (Universal Positive Definiteness).**
*For every $n \in \mathbb{N}$ and every $v \in \mathbb{Z}^n$:*

1. *Positive Semi-Definiteness:* $Q_n(v) \ge 0$ (`cartanEnergy_nonneg`).
2. *Positive Definiteness:* $Q_n(v) = 0 \iff v = 0$ (`cartanEnergy_pos_def`).

### 5.2 Dimension-3 Specialization and Sum-of-Squares

For $n=3$, the Cartan matrix $A_3 = \begin{pmatrix} 2 & -1 & 0 \\ -1 & 2 & -1 \\ 0 & -1 & 2 \end{pmatrix}$ defines the symmetric bilinear form on $\mathbb{Z}^3$:
$$\langle u, v \rangle_{A_3} = 2u_x v_x + 2u_y v_y + 2u_z v_z - (u_x v_y + u_y v_x) - (u_y v_z + u_z v_y)$$

**Theorem 5.2 (Sum-of-Squares Decomposition).**
*For any vector $v = (x, y, z) \in \mathbb{Z}^3$, the quadratic form decomposes as a sum of four perfect squares:*
$$Q(v) = \langle v, v \rangle_{A_3} = x^2 + (x - y)^2 + (y - z)^2 + z^2$$
*Consequently, $Q(v) \ge 0$ for all $v \in \mathbb{Z}^3$, and $Q(v) = 0 \iff v = 0$ (`cartanForm_pos_def`).*

### 5.3 Geometric Invariants and Intrinsic Root Characterization

While the two-sided equivalence $\mathrm{Root}_{A_n} \simeq \mathrm{Facet}_{K_{n+2}} \simeq \mathrm{Diagonal}(n)$ and positive-definiteness of the Dirichlet-Cartan energy are established for all $n \in \mathbb{N}$ (§4.2, §5.1), the intrinsic quadratic-energy root classification is machine-checked specifically for the rank $n=3$ specialization ($A_3$):
- **Root Definition:** A vector $v \in \mathbb{Z}^3$ is an $A_3$ root (`IsRootA3 v`) if and only if $\langle v, v \rangle_{A_3} = 2$.
- **Almost-Positive Roots:** $v$ is an almost-positive root (`IsAlmostPositiveRootA3 v`) if $\langle v, v \rangle_{A_3} = 2$ and either all coordinates are non-negative ($v_x, v_y, v_z \ge 0$) or $v$ is a negative simple root ($v \in \{-\alpha_1, -\alpha_2, -\alpha_3\}$).
- **Exact Classification Theorem:** By bounding the coordinates $|x|, |z| \le 1$ and $|y| \le 2$ via the sum-of-squares decomposition (`root_bounds`), theorem `isAlmostPositiveRootA3_iff` proves that $v$ is an almost-positive root if and only if $v$ is in the image of `rootA3_to_vec3`:
  $$\mathrm{IsAlmostPositiveRootA3}(v) \iff \exists r \in \mathrm{RootA3},\, \mathrm{rootA3\_to\_vec3}(r) = v$$

Under the form $\langle \cdot, \cdot \rangle_{A_3}$, the roots satisfy exact geometric invariants:

1. **Norm Invariance:** Every root has squared norm exactly $2$ (`rootA3_cartan_norm`):
   $$\langle r, r \rangle_{A_3} = 2 \quad \forall r \in \mathrm{Root}_{A_3}$$
2. **Adjacent Shear Strain:** Adjacent simple roots have inner product $\langle \alpha_1, \alpha_2 \rangle = \langle \alpha_2, \alpha_3 \rangle = -1$ (`strain_adjacent_12`).
3. **Orthogonality:** Non-adjacent roots are orthogonal: $\langle \alpha_1, \alpha_3 \rangle = 0$ (`strain_orthogonal_13`).
4. **Coupled Decomposition:** Composite roots decompose with cross-terms: $\langle \alpha_{12}, \alpha_{12} \rangle = \langle \alpha_1, \alpha_1 \rangle + \langle \alpha_2, \alpha_2 \rangle + 2\langle \alpha_1, \alpha_2 \rangle = 2 + 2 - 2 = 2$ (`coupled_strain_alpha12`).

---

# Part III: Path Valuations and Chain Applications

This part studies the data carried by a chain. Section 6 assigns costs and integer labels to its steps. It proves that every full bracket pattern gives the same composite arrow and the same path valuation. The partial bracket patterns have the associahedral face order from Part II.

Section 7 gives an application to subobjects. A finite segment $C_0 \le \cdots \le C_n$ of a filtration is a monotone chain, so the theorem in §6.3 applies to its $n$ arrows. The costs and integer labels are assigned data. The transfinite reconstruction proof uses the subobject order from Part I and the abelian-category assumptions in §7.1. The path-valuation theorem does not require a filtration.

## 6. Path Valuations on Step Sequences and Covering Quivers

### 6.1 Step Sequences and the Travel Monoid

Let $(L, \le)$ be a poset. We define path valuations over sequences of directed lattice steps $s = (u \le v)$ equipped with friction cost $c(s) \in \mathbb{N}$ and integer label $e(s) \in \mathbb{Z}$ (`LatticeStep`). In a discrete covering quiver, these correspond to covering chains $u \lessdot v$; the algebraic monoid structure and concatenation homomorphisms operate generally on arbitrary lists of directed steps.

Let $\mathbf{U}_2(\mathbb{Z})$ denote the multiplicative group of $2 \times 2$ unipotent upper-triangular matrices:
$$\mathbf{U}_2(\mathbb{Z}) = \left\{ \begin{pmatrix} 1 & e \\ 0 & 1 \end{pmatrix} \;\middle|\; e \in \mathbb{Z} \right\}$$
with group multiplication $\begin{pmatrix} 1 & e_1 \\ 0 & 1 \end{pmatrix} \begin{pmatrix} 1 & e_2 \\ 0 & 1 \end{pmatrix} = \begin{pmatrix} 1 & e_1 + e_2 \\ 0 & 1 \end{pmatrix}$. This group is canonically isomorphic to the additive group $(\mathbb{Z}, +)$. In the Lean formalization (`FunctorialGeometry.lean`), $\mathbf{U}_2(\mathbb{Z})$ is modeled directly as the additive group $(\mathbb{Z}, +)$ (`structure Unipotent2`), and all monoid laws and path bounds are proved by `omega` and `linarith`.

**Definition 6.1 (Travel Monoid).** The state space is the direct product monoid $\mathcal{M} = (\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z}) \cong (\mathbb{N}, +) \times (\mathbb{Z}, +)$, where elements are pairs $(a, \mathbf{U})$ of accumulated path cost $a \in \mathbb{N}$ and unipotent shear label $\mathbf{U} \in \mathbf{U}_2(\mathbb{Z})$, with identity $(0, \mathbf{I})$ and composition:
$$(a_1, \mathbf{U}_1) \star (a_2, \mathbf{U}_2) = (a_1 + a_2, \mathbf{U}_1 \mathbf{U}_2)$$

**Definition 6.2 (Path Valuation).** For an elementary step $s = (u \le v)$ with friction cost $c(s) \in \mathbb{N}$ and integer label $e(s) \in \mathbb{Z}$, the step valuation is $\mathbb{T}(s) = (c(s), \begin{pmatrix} 1 & e(s) \\ 0 & 1 \end{pmatrix})$. For any sequence of steps $p = [s_1, \dots, s_k]$, the path valuation is defined by folding across the step list:
$$\mathbb{T}(p) = \mathrm{pathExperience}(p) \in \mathcal{M}$$

### 6.2 Monoid Laws, Concatenation, and Strict Growth

**Theorem 6.3 (Functorial Path Properties).**

1. *Monoid Associativity and Unitality:* The operation $\star$ on $\mathcal{M}$ satisfies associativity $(t_1 \star t_2) \star t_3 = t_1 \star (t_2 \star t_3)$ and two-sided identity $\mathbf{1} \star t = t = t \star \mathbf{1}$.
2. *Path Concatenation Homomorphism:* For any two step sequences $p, q$:
   $$\mathbb{T}(p \mathbin{+\!+} q) = \mathbb{T}(p) \star \mathbb{T}(q)$$
3. *Strict Action Growth:* If an elementary step $s$ has positive cost $c(s) > 0$, the action coordinate strictly increases under composition:
   $$\mathrm{action}(t \star \mathbb{T}(s)) > \mathrm{action}(t)$$

*Proof.* In Lean 4, monoid laws are proven in `TravelExperience.mul_assoc` and `TravelExperience.one_mul` via `omega`. Homomorphic concatenation is proven in `pathExperience_append` by list induction and `foldl_stepExperience`. Strict growth is verified by `action_strictly_increases` via `linarith`. $\blacksquare$

### 6.3 Path Valuations on Associahedral Bracket Patterns

Let $x_0 \le \cdots \le x_n$ be a fixed chain. Assign cost $c_i \in \mathbb{N}$ and integer label $e_i \in \mathbb{Z}$ to the step $x_i \to x_{i+1}$. The declaration `chainSteps` forms the ordered list of these steps. The declaration `evalChainPathBracketing` evaluates a full binary bracket pattern: each leaf gives one step valuation, and each internal node multiplies its two subpath valuations.

**Theorem 6.4 (Fixed-Chain Arrow and Valuation Invariance).** For every $n \ge 1$ and every full bracket pattern $t$ of the fixed labelled chain,
$$\mathbb{T}_t(x,c,e)=\left(\sum_{i=0}^{n-1}c_i,\begin{pmatrix}1&\sum_{i=0}^{n-1}e_i\\0&1\end{pmatrix}\right).$$
Thus any two full bracket patterns give the same path valuation and the same arrow $x_0 \to x_n$. Their partial bracket patterns give the face order $K_n$ under the conventions in §4.1. The combined Lean theorem is `all_Kn_chain_path_valuations`.

*Proof.* Induct on the binary tree. A leaf consumes one step. At an internal node, split the ordered list into a prefix and a suffix according to the left subtree's leaf count. The induction hypotheses identify their bracketed values with their path valuations. The concatenation law then gives the valuation of the whole list (`evalBracketPath_eq`). The list length is exactly $n$, so this applies to every full pattern (`evalChainPathBracketing_eq`). The coordinate sums follow from `pathExperience_action`, `pathExperience_label`, and `chainSteps_valuation`. Thinness gives equality of the composite arrows; the order isomorphism in §4.1 gives the associahedral face order.

**Corollary 6.5 (Unit-Cost Arrow Count).** If every step has cost one, every full bracket pattern has total cost $n$ (`evalChainPathBracketing_unit_cost`). This counts arrows; repeated objects are permitted in the chain.

For example, three steps with costs $(2,3,5)$ and labels $(4,-7,1)$ give total cost $10$ and total label $-2$ under both full bracket patterns. Different chains with the same endpoints can have different valuations. The theorem fixes the chain and its labels; it imposes no endpoint-invariance condition.

At $n=0$, the empty step list has valuation $(0,\mathbf{I})$, and the empty categorical composite is the identity. There is no full binary tree in this case, and $K_0$ remains the empty member by convention.

---

## 7. Application: Transfinite Cellular Filtrations and Basis Discovery

### 7.1 Universe Plumbing, Transfinite Cellular Filtrations, and Stabilization

To avoid the collapse of abelian categories with small colimits into trivial preorders (dictated by Freyd's Theorem when objects and morphisms inhabit the same universe), we formulate the ambient abelian category with universe stratification:
$$\mathcal{A} : \mathrm{Type}(u+1), \qquad \mathrm{Hom}_{\mathcal{A}}(X, Y) : \mathrm{Type}(u)$$
equipped with `[Abelian A]`, `[HasLimitsOfSize.{u, u} A]`, `[HasColimitsOfSize.{u, u} A]`, and `[WellPowered.{u} A]`.

An object $U_0 \in \mathcal{A}$ is *semi-Artinian* if for every proper subobject $C < U_0$, the residual quotient $\mathrm{coker}(C \hookrightarrow U_0)$ contains a simple subobject.

#### Cellular Filtrations vs. Classical Loewy Filtrations

In standard algebra, the classical ascending Loewy series attaches the entire socle (the sum of all simple subobjects) simultaneously at each step: $S_{\alpha+1} / S_\alpha = \mathrm{Soc}(U_0 / S_\alpha)$.
In our formal development, we construct a **fine transfinite cellular filtration**—a one-simple-at-a-time transfinite filtration, a transfinite composition series—where each non-trivial successor step attaches a **single simple cell** $a \hookrightarrow \mathrm{coker}(C_\alpha)$ via categorical pullback. Each non-trivial successor step has a simple quotient.

**Definition 7.1 (Transfinite Cellular Sequence).** The cellular sequence is constructed transfinitely for ordinals $o \in \mathrm{Ordinal}.\{u\}$:

- **Base Case:** $C_0 = \bot$.
- **Successor Step:** $C_{\alpha+1} = C_\alpha$ if $\mathrm{coker}(C_\alpha \hookrightarrow U_0) = 0$; otherwise, choose a simple subobject $a \hookrightarrow \mathrm{coker}(C_\alpha)$ and pull it back to form $C_{\alpha+1} = \mathrm{pb}(a \to \mathrm{coker}(C_\alpha))$.
- **Limit Ordinal:** $C_\lambda = \sup_{\beta < \lambda} C_\beta$.

**Theorem 7.2 (Cellular Length Existence, Reconstruction, and Colimit Vanishing).**
*Let $U_0$ be semi-Artinian. Because the subobject lattice $\mathrm{Sub}(U_0)$ is small (`Small.{u} (Subobject U₀)`), the monotone transfinite sequence $C_\alpha$ must stabilize. Consequently:*

1. *Cellular Length Existence:* There exists an ordinal $\Omega \in \mathrm{Ordinal}.\{u\}$ such that $C_\Omega = \top = U_0$ (`cellular_length_exists`).
2. *Top Reconstruction:* The canonical inclusion morphism $C_\Omega \hookrightarrow U_0$ is an isomorphism (`reconstruction_iso`).
3. *Cellular Short Exact Sequence:* Every non-trivial cellular successor step forms a short exact sequence $0 \longrightarrow C_\alpha \longrightarrow C_{\alpha+1} \longrightarrow a \longrightarrow 0$ (`cellular_shortExact`), presenting a length-1 extension.

**Corollary 7.3 (Vanishing Residual Colimit).** Restrict the residual diagram to the small filtered category $\mathrm{OrdinalInterval}(\Omega) := \mathrm{Shrink}.\{u\}(\{b \le \Omega\})$. Its terminal object is $\Omega$, where $\mathrm{coker}(C_\Omega \hookrightarrow U_0) \cong 0$. Thus the colimit of the residual diagram is zero (`cellular_residual_colimit_vanishes`):
   $$\varinjlim_{j \in \mathrm{OrdinalInterval}(\Omega)} \mathrm{coker}(C_j \hookrightarrow U_0) \cong 0$$

### 7.2 Well-Founded Basis Selection

In a discrete complete lattice $L$ generated by an indexed set $\{e(j) \mid j \in J\}$ under a well-founded priority order $(J, \le)$, the greedy choice function:
$$\phi(x) = \min_{<} \{j \in J \mid e(j) \not\le x\}$$
is well-defined for all $x < \top$. It satisfies the **novelty property**: $e(\phi(x)) \not\le x$, guaranteeing strict progress at every transfinite step toward $\top = \bigvee_{j} e(j)$. The transfinite supremum $\mathrm{sieveOutput} = \sup_{o} x(o)$ defines a supremum with the expected order properties, satisfying $x(o) \le \mathrm{sieveOutput}$ (`xSeq_le_sieveOutput`) and least upper bound characterization $\mathrm{sieveOutput} \le x \iff \forall o,\, x(o) \le x$ (`sieveOutput_is_lub`).

---

## 8. Lean 4 Formalization and Machine Verification

The entry point is [`FunctorialGeometry.lean`](math_project/MathProject/FunctorialGeometry.lean). It imports the general associahedron proofs through six modules:

- [`AssociahedralComposition.lean`](math_project/MathProject/AssociahedralComposition.lean): bracket and polygon orders, full-bracketing count, and chain evaluation.
- [`AssociahedralTrees.lean`](math_project/MathProject/AssociahedralTrees.lean): tree completion, vertex correspondence, rotations, and combinatorial counts.
- [`AssociahedralRealization.lean`](math_project/MathProject/AssociahedralRealization.lean): Loday coordinates, convex hull, supporting inequalities, and actual extreme points.
- [`AssociahedralFaces.lean`](math_project/MathProject/AssociahedralFaces.lean): certificates for all linear functionals and the complete supporting-face order isomorphism.
- [`AssociahedralDimension.lean`](math_project/MathProject/AssociahedralDimension.lean): actual affine dimension, geometric counts, and the combined theorem for poset chains.
- [`AssociahedralFacetProducts.lean`](math_project/MathProject/AssociahedralFacetProducts.lean): facet product face orders, convex subface orders, and the pentagon and square shapes and counts for $K_5$.

[`CheckAssociahedra.lean`](math_project/MathProject/CheckAssociahedra.lean) checks the axiom dependencies and the small geometric cases. [`CheckPathValuations.lean`](math_project/MathProject/CheckPathValuations.lean) audits the path-valuation theorems and checks labelled examples and the empty path. [`CheckFacetProducts.lean`](math_project/MathProject/CheckFacetProducts.lean) audits the facet product proofs and checks the root-to-shape conclusions.

### 8.1 Design Principles and Axiomatic Foundations

The formal development follows four structural principles:

1. **Categorical Integration with Mathlib:** Rather than using ad-hoc posetal order structures, thin categories and subobject lattices are expressed directly through Mathlib's native category theory library (`CategoryTheory.Subobject`, `CategoryTheory.Abelian`, `CategoryTheory.Monad`, and `CategoryTheory.Limits`).
2. **Constructive Computational Core:** Discrete and algebraic structures—including the travel monoid $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$, the Tamari poset $\mathcal{T}_4$, the general $A_n \leftrightarrow K_{n+2}$ equivalence, the polygon diagonal mapping $\mathrm{Diagonal}(n)$, the $A_3 \leftrightarrow K_5$ root-facet bijection, and the Cartan quadratic forms—are defined constructively with `DecidableEq` instances and verified by computation (`rfl`, `decide`, `ring`, `omega`).
3. **Classical Homological Framework:** Abstract abelian categories and transfinite ordinals use standard classical logic (`Classical.choice`, `open Classical`) for subobject selection and non-constructive colimits (Theorem 7.2).
4. **Cellular Sequence Nomenclature:** In the Lean formalization, the declarations `cellularSequence` and `cellularLength` name this one-simple-at-a-time transfinite cellular sequence and its stabilization length, a transfinite composition series.

The `#print axioms` command confirms that all declarations compile without `sorry` placeholders and depend exclusively on Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

### 8.2 Paper-to-Code Correspondence Matrix

| Paper Statement | Mathematical Concept | Lean 4 Declaration | Proof Technique / Tactic |
| :--- | :--- | :--- | :--- |
| **Proposition 2.1** | Subsingleton homs, monic/epic collapse, split extensions | [`thin_mono`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L98), [`thin_epi`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L104), [`thin_extension_splits`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L114) | `Subsingleton.elim` |
| **Section 2.2** | Meets as categorical products, joins as coproducts | [`meet_universal`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L153), [`join_universal`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L161), [`subobject_mono`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L175) | `le_inf`, `sup_le`, `inferInstance` |
| **Proposition 2.2 / Lemma 2.3** | Closure operators as idempotent monads & Galois induction | [`ClosureOperator.toMonad`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L129), `GaloisConnection.closureOperator` (Mathlib) | `CategoryTheory.Monad`, `thin_hom_unique`, `GaloisConnection` |
| **Lemma 3.2** | Submodular defect $\Delta \ge 0$, modularity criterion $\Delta = 0$ | [`submodularDefect`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L197), [`defect_nonneg`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L201), [`defect_zero_iff_modular`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L208) | `linarith` |
| **Section 3.2** | Meet interaction realized as categorical meet | [`meetInteraction`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L223), [`meetInteraction_comm`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L225), [`meetInteraction_universal`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L231) | Infimum symmetry and universal properties |
| **Section 4.1** | Tamari $\mathcal{T}_4$ Catalan cardinality $C_3 = 5$ | [`tamari_le`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1089), [`tamari4_card`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1188) | Finite case exhaustion (`rfl`) |
| **Theorem 4.0** | Bracket-to-diagonal compatibility and face order for every arity | `bracketCompatible_iff_noncrossing`, `all_Kn_orderIso`, `all_Kn_categoryEquivalence` | Endpoint inequalities, finite-set maps, `OrderIso` |
| **Theorem 4.0** | All bracket patterns of a finite chain give the same arrow | `all_Kn_chain_composites`, `all_Kn_thin_composition` | Recursive categorical composition, `Subsingleton.elim` |
| **Section 4.1** | Full binary bracketing count for every positive arity | `fullBracketing_card`, `fullBracketing_card_formula` | Mathlib binary-tree enumeration and Catalan formula |
| **Theorem 4.0.1** | Convex face order, actual affine dimension, and geometric counts for every rank | `polygon_loday_face_orderIso`, `Loday_affine_dimension`, `Loday_geometric_vertex_count`, `Loday_geometric_facet_count`, `all_Kn_poset_realization` | Interval inequalities, normal certificates, tree rotations, affine-span rank |
| **Theorem 4.0.2** | Each facet has the product face order of two smaller associahedra | `polygonFacet_product_orderIso`, `Loday_facet_geometric_product_orderIso` | Split the polygon, preserve crossings, restrict the supporting-face order |
| **Theorem 4.1** | Two-sided geometric equivalence $\mathrm{Root}_{A_n} \simeq \mathrm{Facet}_{K_{n+2}} \simeq \mathrm{Diagonal}(n)$ | [`facetKn2_diagonal_equiv`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1286), [`rootAn_facetKn2_equiv`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1502), [`rootAn_diagonal_equiv`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1509) | `Fin.isLt`, `omega`, two-sided inverse proofs |
| **Theorem 4.3** | Constructive bijection $\Phi_{\ge -1}(A_3) \simeq \mathrm{Facets}(K_5)$ & Cyclic Length Theorems | [`rootA3_facetK5_equiv`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1717), [`rootA3_cyclic_length_pentagon`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1720), [`rootA3_cyclic_length_square`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1726) | Constructive two-sided inverse, `cases`, `rfl` |
| **Section 4.3** | Actual pentagonal and square facet types, with counts six and three | `rootA3_geometric_pentagonal_facet`, `rootA3_geometric_square_facet`, `Loday_K5_pentagonal_facet_count`, `Loday_K5_square_facet_count` | Facet product order, cyclic length, transfer to convex supporting faces |
| **Theorem 5.1** | Universal positive-definite $A_n$ Dirichlet-Cartan energy | [`cartanEnergy_nonneg`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1791), [`cartanEnergy_pos_def`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1797) | `Finset.sum_eq_zero_iff_of_nonneg`, induction, `omega` |
| **Section 5.2** | Sum-of-squares $A_3$ Cartan energy | [`cartanForm_sum_of_squares`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1865), [`cartanForm_pos_def`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1877) | `ring`, `nlinarith [sq_nonneg]` |
| **Section 5.3** | Intrinsic $A_3$ root classification, norm invariance ($=2$), couplings ($-1, 0$) | [`root_bounds`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1935), [`isAlmostPositiveRootA3_iff`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1982), [`rootA3_to_vec3_injective`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1977), [`rootA3_cartan_norm`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L2036), [`strain_adjacent_12`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1901) | Sum-of-squares bounds, `nlinarith`, case analysis, `rfl` |
| **Theorem 6.3** | Travel monoid laws, path concatenation, strict growth | [`Unipotent2`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L248), [`TravelExperience`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L279), [`pathExperience_append`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L349), [`action_strictly_increases`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L357) | Additive group model $(\mathbb{Z}, +)$, `omega`, `linarith` |
| **Theorem 6.4** | Fixed-chain arrow and valuation invariance on every full bracket pattern | `evalBracketPath_eq`, `evalChainPathBracketing_eq`, `chainSteps_valuation`, `all_Kn_chain_path_valuations` | Binary-tree induction, list splitting, concatenation, thinness |
| **Corollary 6.5** | Unit step costs count the arrows | `evalChainPathBracketing_unit_cost` | Finite sum of ones |
| **Theorem 7.2 (1–2)** | Cellular length existence $\Omega$, stabilization, top reconstruction | [`cellularSequence_mono`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L606), [`cellular_length_exists`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L675), [`reconstruction`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L687), [`reconstruction_iso`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L691) | `Ordinal.limitRecOn`, `eventuallyConst`, `Subobject.top_arrow_isIso` |
| **Theorem 7.2 (3)** | Cellular Short Exact Sequence | [`cellularShortComplex`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L820), [`cellular_shortExact`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L893) | `ShortComplex.exact_of_f_is_kernel`, `pullback` |
| **Corollary 7.3** | Vanishing residual colimit over $\mathrm{OrdinalInterval}$ | [`cellularIntervalFunctor`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L764), [`cellular_residual_colimit_vanishes`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L771) | Filtered colimit absorption, `isZero_cokernel_of_epi` |
| **Section 7.2** | Well-founded basis selection, novelty property, and sieve supremum | [`candidates_nonempty`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L912), [`fixedPriorityPhi`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L924), [`novelty_of_fixedPriorityPhi`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L929), [`sieveOutput`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L941), [`xSeq_le_sieveOutput`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1024), [`sieveOutput_is_lub`](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/FunctorialGeometry.lean#L1028) | `WellFounded.min_mem`, `le_iSup`, `iSup_le_iff` |

### 8.3 Compilation and Machine Verification

The file `FunctorialGeometry.lean` was verified against Lean 4 (version `v4.33.1`) and Mathlib. The build process runs without errors (note: some linters are disabled):
```bash
lake build MathProject.FunctorialGeometry
lake build MathProject.CheckPathValuations MathProject.CheckAssociahedra MathProject.CheckFacetProducts
```

The axiomatic dependency commands:
```lean
#print axioms cellular_length_exists
#print axioms cellular_residual_colimit_vanishes
#print axioms facetKn2_diagonal_equiv
#print axioms rootAn_diagonal_equiv
#print axioms rootA3_facetK5_equiv
#print axioms isAlmostPositiveRootA3_iff
#print axioms cartanEnergy_pos_def
#print axioms cellular_shortExact
#print axioms cyclic_length_count
#print axioms all_Kn_thin_composition
#print axioms all_Kn_categoryEquivalence
#print axioms fullBracketing_card_formula
#print axioms fullBracketing_vertex_equiv
#print axioms polygon_loday_face_orderIso
#print axioms Loday_affine_dimension
#print axioms Loday_geometric_vertex_count
#print axioms Loday_geometric_facet_count
#print axioms all_Kn_poset_realization
#print axioms evalBracketPath_eq
#print axioms chainSteps_valuation
#print axioms evalChainPathBracketing_unit_cost
#print axioms all_Kn_chain_path_valuations
#print axioms Loday_facet_geometric_product_orderIso
#print axioms Loday_K5_pentagonal_facet_count
#print axioms Loday_K5_square_facet_count
#print axioms rootA3_geometric_pentagonal_facet
#print axioms rootA3_geometric_square_facet
```
reduce exclusively to the standard core foundations `[propext, Classical.choice, Quot.sound]`.

---

## 9. Conclusion

We have established a formal categorical and geometric framework for partially ordered sets and subobject lattices:

1. **Category Structure:** Meets, joins, and closure operators emerge as limits, colimits, and idempotent monads (`CategoryTheory.Monad`).
2. **Defect Theory:** Modularity of valuations is governed by the non-negative defect $\Delta \ge 0$, whose vanishing characterizes modular rank functions.
3. **Associahedral Presentations:** For every arity, the bracket and polygon face models have isomorphic orders. All full bracket patterns of a poset chain give the same composite arrow. The Lean development also identifies the facet labels with $A_n$ almost-positive roots and polygon diagonals, classifies the $A_3$ labels by cyclic length, proves their pentagonal and square facet types and counts, and proves Cartan norm 2. The convex realization, complete supporting-face order, actual affine dimension, and geometric counts are now proved for every rank, including the rank-zero point.
4. **Monoidal Dynamics:** Path valuations into $(\mathbb{N}, +) \times \mathbf{U}_2(\mathbb{Z})$ capture accumulated cost and unipotent shear labels with homomorphic path concatenation. For every fixed labelled chain, all full bracket patterns give the same arrow and the same valuation.
5. **Filtration Limits:** Semi-Artinian objects in universe-stratified abelian categories admit transfinite cellular reconstructions with vanishing residual colimits over restricted ordinal intervals at stabilization.

All results compile in Lean 4 without `sorry` placeholders and depend solely on standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## References

1. Stasheff, J. D. (1963). *Homotopy associativity of $H$-spaces. I, II.* Trans. Amer. Math. Soc., 108:275–312.
2. Mac Lane, S. (1998). *Categories for the Working Mathematician.* Springer Graduate Texts in Mathematics, 2nd ed.
3. Fomin, S., & Zelevinsky, A. (2003). *$Y$-systems and generalized associahedra.* Ann. of Math. (2), 158(3):977–1018.
4. Freyd, P. (1964). *Abelian Categories: An Introduction to the Theory of Functors.* Harper & Row.
5. Loewy, A. (1905). *Über die Reduktion algebraischer Gleichungen durch Adjunktion insbesondere reeller Radikale.* Math. Ann., 60(3):342–352.
6. The mathlib Community. (2020). *The Lean Mathematical Library.* In Proc. CPP 2020, pages 367–381.
7. Lee, C. W. (1989). *The Associahedron and Triangulations of the n-gon.* European Journal of Combinatorics, 10(6):551–560.
8. Chapoton, F., Fomin, S., & Zelevinsky, A. (2002). *Polytopal realizations of generalized associahedra.* Canadian Mathematical Bulletin, 45(4):537–566.
9. Marsh, R., Reineke, M., & Zelevinsky, A. (2003). *Generalized associahedra via quiver representations.* Trans. Amer. Math. Soc., 355(10):4171–4186.

10. Loday, J.-L. (2004). *Realization of the Stasheff polytope.* Archiv der Mathematik, 83:267–278. [Preprint](https://arxiv.org/abs/math/0212126).
