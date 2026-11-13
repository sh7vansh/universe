# Supplementary Lattice Notes: Combinatorial Theory of Sub-Associahedral Embeddings

**Companion to:** [thin-category-lattice.md](thin-category-lattice.md)

Let $A_\infty$ denote the non-symmetric operad of homotopy associative algebras (the cellular resolution of the associative operad $\mathcal{A}ss$), where the component of arity $N \ge 2$ is represented geometrically by the Stasheff associahedron $K_N$, whose $0$-skeleton $\mathrm{Vert}(K_N)$ indexes all binary parenthesizations of the $N$-ary operation in $\mathcal{A}ss$.

> **Notation Remark (Alignment with [thin-category-lattice.md](thin-category-lattice.md)):** In the main paper, $\mathcal{T}_4$ denotes the Tamari lattice on $C_3 = 5$ vertices, and proper bracketings use $0$-indexed half-open intervals $[a, b)$ on $\{0, \dots, N\}$ with $(a, b) \ne (0, N)$ (Theorem 4.0). Here, $\mathcal{T}_N$ denotes the *set* of planar full binary trees with $N$ ordered leaves, and we use $1$-indexed closed intervals $I = [i, i + k - 1] \subseteq [N]$ (corresponding to $[i - 1, i + k - 1)$ in $0$-indexed notation).

---

## 1. Definitions and Notation

* Let $\mathcal{T}_N$ denote the set of planar full binary trees with $N \ge 1$ ordered leaves (for $N \ge 2$, the $0$-skeleton $\mathrm{Vert}(K_N)$).
* Its cardinality is the Catalan number:
  $$|\mathcal{T}_N| = C_{N-1} = \frac{1}{N}\binom{2N - 2}{N - 1}.$$
* Let $[N] = \{1, 2, \dots, N\}$ denote the totally ordered set of leaves.
* For $2 \le k \le N$, a contiguous sub-interval of arity $k$ is a set:
  $$I = [i,\, i + k - 1] \subseteq [N], \qquad 1 \le i \le N - k + 1.$$
  Let $\mathcal{I}_k(N)$ denote the set of all such contiguous intervals. Clearly:
  $$|\mathcal{I}_k(N)| = N - k + 1.$$

**Definition 1.1 (Sub-Tree Support).**
For $T \in \mathcal{T}_N$ and $I \in \mathcal{I}_k(N)$, we say that $I$ forms a *complete sub-tree component* in $T$ (denoted $I \triangleleft T$) if there exists an internal node $v \in T$ whose set of descendant leaves is precisely $I$. Because every internal node in a full binary tree has two nonempty subtrees, distinct internal nodes have distinct descendant leaf sets; hence at most one node $v \in T$ can witness $I \triangleleft T$.

*Geometric interpretation:* For **proper** intervals ($2 \le k \le N - 1$, with $N \ge 3$), $I \triangleleft T$ corresponds to the vertex $T$ lying on the supporting boundary facet $F_I$ of $K_N$ (of combinatorial type $K_k \times K_{N-k+1}$, Theorem 4.0.2 of [thin-category-lattice.md](thin-category-lattice.md#L213)) defined by the internal diagonal separating $I$ in an $(N+1)$-gon. At the boundary case $k = N$, $I = [1, N]$ corresponds to the root of $T$ and the entire polytope $K_N$ itself rather than a proper boundary facet.

---

## 2. Fiber Cardinality of a Fixed Interval

**Theorem 2.1 (Operadic Factorization).**
*For any fixed contiguous interval $I = [i, i + k - 1] \in \mathcal{I}_k(N)$ of length $k$ ($2 \le k \le N$), the number of trees in $\mathcal{T}_N$ admitting $I$ as a complete sub-tree component is:*
$$\#\{T \in \mathcal{T}_N \mid I \triangleleft T\} = C_{k-1} \cdot C_{N-k}.$$

*Proof.*
Set $j = i$. By operadic composition of planar trees, any tree $T \in \mathcal{T}_N$ satisfying $I \triangleleft T$ factors uniquely via the grafting map at the $j$-th leaf:
$$\circ_j : \mathcal{T}_{N-k+1} \times \mathcal{T}_k \xrightarrow{\ \sim\ } \{ T \in \mathcal{T}_N \mid I \triangleleft T \},$$
where:

1. $T_{\mathrm{in}} \in \mathcal{T}_k$ is the internal binary sub-tree spanning the $k$ leaves of $I$. The number of such trees is $|\mathcal{T}_k| = C_{k-1}$.
2. $T_{\mathrm{out}} \in \mathcal{T}_{N-k+1}$ is the outer quotient tree obtained by contracting the entire sub-tree rooted at $v$ into a single composite leaf at position $j = i$. The number of such trees is $|\mathcal{T}_{N-k+1}| = C_{(N-k+1)-1} = C_{N-k}$.

Because grafting at leaf $j$ is an exact bijection of finite sets:
$$\#\{T \in \mathcal{T}_N \mid I \triangleleft T\} = |\mathcal{T}_k| \cdot |\mathcal{T}_{N-k+1}| = C_{k-1} \cdot C_{N-k}. \quad \blacksquare$$

---

## 3. The Global Embedding Sum

**Theorem 3.1 (Global Sub-Tree Component Multiplicity).**
*For $2 \le k \le N$, the total number of complete sub-tree components of arity $k$ across all trees in $\mathcal{T}_N$ (equivalently, for $2 \le k \le N - 1$, the total number of vertex–facet incidences $(T, F_I)$ with $F_I \cong K_k \times K_{N-k+1}$ across all vertices of $K_N$) is:*
$$\Phi(N, k) := \sum_{I \in \mathcal{I}_k(N)} \#\{T \in \mathcal{T}_N \mid I \triangleleft T\} = C_{k-1} \binom{2(N - k)}{N - k}.$$

*Proof.*
Summing Theorem 2.1 over all $I \in \mathcal{I}_k(N)$:
$$\Phi(N, k) = \sum_{I \in \mathcal{I}_k(N)} C_{k-1} \cdot C_{N-k} = |\mathcal{I}_k(N)| \cdot C_{k-1} \cdot C_{N-k}.$$
Substitute $|\mathcal{I}_k(N)| = N - k + 1$ and the explicit Catalan formula $C_{N-k} = \frac{1}{N - k + 1}\binom{2(N - k)}{N - k}$:
$$\Phi(N, k) = (N - k + 1) \cdot C_{k-1} \cdot \left[\frac{1}{N - k + 1}\binom{2(N - k)}{N - k}\right].$$
The algebraic factor $(N - k + 1)$ cancels identically:
$$\Phi(N, k) = C_{k-1} \binom{2(N - k)}{N - k}. \quad \blacksquare$$

---

## 4. Corollary: Minimal Binary Generators ($k = 2$)

**Corollary 4.1 (Central Binomial Multiplicity).**
*For elementary binary composition nodes ($k = 2$, corresponding to $K_2$, i.e. cherries in $\mathcal{T}_N$), the global multiplicity simplifies to the central binomial coefficient:*
$$\Phi(N, 2) = \binom{2N - 4}{N - 2}.$$

*Proof.*
For $k = 2$, $C_{k-1} = C_1 = 1$. Substituting into Theorem 3.1 gives $\Phi(N, 2) = \binom{2N - 4}{N - 2}$. $\blacksquare$

---

## 5. Average Subtree Density and Asymptotics

**Theorem 5.1 (Expected Density per Vertex).**
*Equip $\mathcal{T}_N$ with the uniform probability measure. The expected number of complete sub-trees of arity $k$ in a randomly chosen tree $T \in \mathcal{T}_N$ is:*
$$\mathbb{E}[n_k](N) = \frac{\Phi(N, k)}{|\mathcal{T}_N|} = \frac{C_{k-1}\binom{2N - 2k}{N - k}}{\frac{1}{N}\binom{2N - 2}{N - 1}}.$$

**Theorem 5.2 (Asymptotic Scaling Law).**
*In the limit $N \to \infty$ for fixed $k \ge 2$, the expected density scales linearly with $N$:*
$$\mathbb{E}[n_k](N) = \frac{C_{k-1}}{4^{k-1}}\,N + \frac{C_{k-1}(k - 1)}{2 \cdot 4^{k-1}} + \mathcal{O}\!\left(\frac{1}{N}\right) = \frac{C_{k-1}}{4^{k-1}}\,N + \mathcal{O}(1).$$

*Proof.*
For each $m \ge 0$, the ratio of consecutive central binomial coefficients satisfies:
$$\frac{\binom{2m}{m}}{\binom{2m + 2}{m + 1}} = \frac{(m + 1)^2}{(2m + 2)(2m + 1)} = \frac{m + 1}{2(2m + 1)} = \frac{1}{4}\left(1 + \frac{1}{2m + 1}\right).$$
Telescoping from $m = N - k$ to $m = N - 2$ ($k - 1$ steps) gives the exact product:
$$\frac{\binom{2N - 2k}{N - k}}{\binom{2N - 2}{N - 1}} = \prod_{j=1}^{k-1} \frac{1}{4}\left(1 + \frac{1}{2(N - j) - 1}\right) = \frac{1}{4^{k-1}}\left(1 + \frac{k - 1}{2N} + \mathcal{O}\!\left(\frac{1}{N^2}\right)\right).$$
Multiplying by $C_{k-1} N$ from Theorem 5.1 yields:
$$\mathbb{E}[n_k](N) = \frac{C_{k-1}}{4^{k-1}}\,N + \frac{C_{k-1}(k - 1)}{2 \cdot 4^{k-1}} + \mathcal{O}\!\left(\frac{1}{N}\right) = \frac{C_{k-1}}{4^{k-1}}\,N + \mathcal{O}(1). \quad \blacksquare$$

---

## 6. Lean 4 Formalization and Machine Verification

All results above are formalized without `sorry` placeholders in Lean 4 (`v4.35.0`, Mathlib) and depend solely on the standard core axioms `[propext, Classical.choice, Quot.sound]`:

* **Main module:** [`AssociahedralSubtreeEmbeddings.lean`](math_project/MathProject/AssociahedralSubtreeEmbeddings.lean)
* **Axiom audit & small-case checks:** [`CheckSubtreeEmbeddings.lean`](math_project/MathProject/CheckSubtreeEmbeddings.lean)

| Paper Statement | Mathematical Concept | Lean 4 Declaration |
| :--- | :--- | :--- |
| **Definition 1.1** | Sub-tree support, proper-interval bridge to `PartialBracketing N`, Loday vertex–facet incidence, and $F_I \cong K_k \times K_{N-k+1}$ | `SubtreeSupport`, `subtreeSupport_iff_mem_partialBracketing`, `subtreeSupport_iff_loday_vertex_on_facet`, `subtreeFacet_product_orderIso` |
| **Theorem 2.1** | Explicit grafting/extraction bijection $\mathcal{T}_{N-k+1} \times \mathcal{T}_k \simeq \{T \in \mathcal{T}_N \mid I \triangleleft T\}$ and fiber cardinality $C_{k-1} C_{N-k}$ | `graftTree`, `extractAt`, `contractAt`, `operadicFactorizationEquiv`, `subtree_fiber_card` |
| **Theorem 3.1** | Double counting across intervals and trees; Loday vertex–facet incidence sum; global multiplicity $\Phi(N, k) = C_{k-1}\binom{2(N-k)}{N-k}$ | `globalSubtreeMultiplicity`, `globalSubtreeMultiplicity_eq_tree_sum`, `globalSubtreeMultiplicity_eq_loday_incidence`, `globalSubtreeMultiplicity_eq` |
| **Corollary 4.1** | Minimal binary generators ($k = 2$): $\Phi(N, 2) = \binom{2N-4}{N-2}$ | `globalSubtreeMultiplicity_k2` |
| **Theorem 5.1** | Average over trees, `MeasureTheory.Measure.uniformOfFinset` expectation form, and exact closed-form density $\mathbb{E}[n_k](N)$ | `expectedSubtreeDensity`, `expectedSubtreeDensity_eq_tree_avg`, `expectedSubtreeDensity_eq_uniform_expectation`, `expectedSubtreeDensity_eq` |
| **Theorem 5.2** | Limit $\mathbb{E}[n_k](N) - \frac{C_{k-1}}{4^{k-1}} N \to \frac{C_{k-1}(k-1)}{2 \cdot 4^{k-1}}$, $+\,\mathcal{O}(1)$ bound, and exact $+\,\mathcal{O}(1/N)$ remainder bound | `expectedSubtreeDensity_sub_linear_tendsto`, `expectedSubtreeDensity_asymptotic`, `expectedSubtreeDensity_asymptotic_inv` |

Verified with:
```bash
lake build MathProject.AssociahedralSubtreeEmbeddings MathProject.CheckSubtreeEmbeddings
```
