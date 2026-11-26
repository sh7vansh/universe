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

## 6. Second Moment, Variance, and Concentration

While Theorem 5.2 establishes that the *mean* number of complete $k$-leaf sub-trees scales as $p_k N$ where
$$p_k := \frac{C_{k-1}}{4^{k-1}},$$
a natural second-order question is whether a typical tree $T \in \mathcal{T}_N$ actually exhibits density $n_k(T)/N \approx p_k$, or whether large fluctuations occur across the associahedron. This is resolved by extending the operadic factorization of Theorem 2.1 to pairs of sites.

### 6.1 Two-Site Operadic Factorization and Pair Multiplicity

Consider two intervals $I = [i, i + k)$ and $J = [j, j + k)$ of equal width $k \ge 2$ inside $\{0, \dots, N - 1\}$. By tree compatibility (`SpanCompatible`), two distinct intervals of the same length $k$ cannot strictly nest, so any two distinct $k$-leaf sub-trees in the same tree $T \in \mathcal{T}_N$ must have disjoint leaf supports ($i + k \le j$ or $j + k \le i$). Contracting both disjoint supports yields a reduced quotient tree in $\mathcal{T}_{N - 2k + 2}$.

**Theorem 6.1 (Two-Site Operadic Factorization).**
*For any disjoint intervals $I = [i, i+k)$ and $J = [j, j+k)$ of width $k \ge 2$ inside $\{0, \dots, N-1\}$ (so $i + k \le j$ or $j + k \le i$), there is an explicit bijection:*
$$\mathcal{T}_{N - 2k + 2} \times \mathcal{T}_k \times \mathcal{T}_k \;\simeq\; \{ T \in \mathcal{T}_N \mid I \triangleleft T \text{ and } J \triangleleft T \},$$
*and consequently the joint fiber cardinality depends only on $N$ and $k$:*
$$|\{ T \in \mathcal{T}_N \mid I \triangleleft T \text{ and } J \triangleleft T \}| = C_{k-1}^2 \, C_{N - 2k + 1}.$$

*Proof.*
Apply Theorem 2.1 first at the right-most site (say $J$ when $i + k \le j$) to factor out its local $k$-leaf tree, preserving the span $I$ inside the contracted quotient tree $T' \in \mathcal{T}_{N-k+1}$. Applying Theorem 2.1 a second time at $I$ yields the triple $(Q, S_I, S_J) \in \mathcal{T}_{N-2k+2} \times \mathcal{T}_k \times \mathcal{T}_k$. Taking cardinalities gives $C_{N-2k+1} \cdot C_{k-1} \cdot C_{k-1}$. For $j + k \le i$, symmetry under swapping $I$ and $J$ gives the same count. $\blacksquare$

**Theorem 6.2 (Global Second Factorial Multiplicity).**
*Let $\Phi_2(N, k) := \sum_{T \in \mathcal{T}_N} n_k(T)\big(n_k(T) - 1\big)$ be the global ordered-pair multiplicity of distinct $k$-leaf sub-trees across $\mathcal{T}_N$. For $k \ge 2$:*
$$\Phi_2(N, k) = \begin{cases} 0 & \text{if } N < 2k, \\ (N - 2k + 1)\,C_{k-1}^2 \dbinom{2(N - 2k + 1)}{N - 2k + 1} & \text{if } N \ge 2k. \end{cases}$$

*Proof.*
When $N < 2k$, no two disjoint $k$-intervals fit in $\{0, \dots, N-1\}$, so every tree has $n_k(T) \le 1$ and $n_k(T)(n_k(T) - 1) = 0$. For $N \ge 2k$, reversing the order of summation counts all ordered pairs $(I, J)$ of disjoint $k$-intervals inside $\{0, \dots, N - 1\}$. There are $(N - 2k + 1)(N - 2k + 2)$ such ordered pairs, each with fiber size $C_{k-1}^2 C_{N - 2k + 1}$ by Theorem 6.1. Using $(m + 1) C_m = \binom{2m}{m}$ with $m = N - 2k + 1$ yields the stated closed form. $\blacksquare$

### 6.2 Exact Second Moment and Linear Variance Scaling

Dividing Theorem 6.2 by $|\mathcal{T}_N| = C_{N-1}$ and adding $\mathbb{E}[n_k](N)$ gives the exact second moment for $N \ge 2k$:
$$\mathbb{E}[n_k^2](N) = C_{k-1}^2 \, N (N - 2k + 1) \frac{\binom{2(N - 2k + 1)}{N - 2k + 1}}{\binom{2N - 2}{N - 1}} + \mathbb{E}[n_k](N),$$
and thus the variance $\mathrm{Var}(n_k)(N) := \mathbb{E}[n_k^2](N) - \mathbb{E}[n_k](N)^2$.

**Proposition 6.3 (Exact Cherry Variance, $k = 2$).**
*For every $N \ge 3$, the variance of the number of $2$-leaf cherries $n_2(T)$ under the uniform measure on $\mathcal{T}_N$ is given by the exact rational function:*
$$\mathrm{Var}(n_2)(N) = \frac{N(N - 1)(N - 2)(N - 3)}{2(2N - 3)^2(2N - 5)} = \frac{1}{16}N - \frac{1}{32} + \mathcal{O}\!\left(\frac{1}{N}\right).$$

*In particular, for $N = 3$ every tree in $\mathcal{T}_3$ has $n_2(T) = 1$ ($\mathrm{Var}(n_2)(3) = 0$), while for $N = 4$ we have $\mathrm{Var}(n_2)(4) = \frac{4}{25}$.*

**Theorem 6.4 (Linear Variance Scaling for Fixed Arity $k \ge 2$).**
*For every fixed $k \ge 2$, the $N^2$ leading terms in $\mathbb{E}[n_k^2](N)$ and $\mathbb{E}[n_k](N)^2$ cancel identically, and the variance grows linearly with strictly positive slope:*
$$\mathrm{Var}(n_k)(N) = \Big(p_k - (2k - 1) p_k^2\Big) N + C_k + o(1) \qquad (N \to \infty),$$
*where $p_k = \frac{C_{k-1}}{4^{k-1}}$ and $p_k - (2k - 1) p_k^2 > 0$ for all $k \ge 2$. In particular, $\mathrm{Var}(n_k)(N)/N \to p_k - (2k - 1) p_k^2$ and $\mathrm{Var}(n_k)(N) = \mathcal{O}(N)$.*

*Proof sketch.*
From the exact central binomial expansion
$$\frac{\binom{2(N - m - 1)}{N - m - 1}}{\binom{2N - 2}{N - 1}} = \frac{1}{4^m}\left(1 + \frac{m}{2N} + \mathcal{O}\!\left(\frac{1}{N^2}\right)\right)$$
applied at $m = k - 1$ (for $\mathbb{E}[n_k]$) and $m = 2k - 2$ (for $\mathbb{E}[n_k(n_k-1)]$), the quadratic terms are both $p_k^2 N^2$. Collecting the linear coefficients gives
$$\big(p_k^2 (k - 1) - (2k - 1) p_k^2 + p_k\big) N - p_k^2(k - 1)N = \big(p_k - (2k - 1)p_k^2\big)N.$$
For positivity, note that for $k = 2$, $(2k - 1) p_k = 3 \cdot \frac{1}{4} = \frac{3}{4} < 1$, and by the Catalan recurrence $C_m = \frac{4m - 2}{m + 1} C_{m-1}$, the sequence $(2k - 1) p_k$ decreases strictly to $(2k - 1) p_k \le \frac{3}{4} < 1$ for all $k \ge 2$, forcing $p_k(1 - (2k - 1)p_k) > 0$. $\blacksquare$

### 6.3 Chebyshev Concentration of Sub-Tree Density

Because the standard deviation $\sqrt{\mathrm{Var}(n_k)(N)} = \mathcal{O}(\sqrt{N})$ is strictly sub-linear relative to the mean $\mathbb{E}[n_k](N) \sim p_k N$, the empirical density $n_k(T)/N$ concentrates sharply around $p_k$.

**Theorem 6.5 (Concentration Around Asymptotic Density).**
*For every $k \ge 2$, $N \ge k$, and $\varepsilon > 0$:*
$$\mathbb{P}_{T \in \mathcal{T}_N}\!\left(\left|\frac{n_k(T)}{N} - p_k\right| \ge \varepsilon\right) \le \frac{\mathrm{Var}(n_k)(N) + \big(\mathbb{E}[n_k](N) - p_k N\big)^2}{\varepsilon^2 N^2}.$$
*Since $\mathrm{Var}(n_k)(N) = \mathcal{O}(N)$ (Theorem 6.4) and $\mathbb{E}[n_k](N) - p_k N = \mathcal{O}(1)$ (Theorem 5.2), it follows that for every fixed $k \ge 2$ and $\varepsilon > 0$:*
$$\lim_{N \to \infty} \mathbb{P}_{T \in \mathcal{T}_N}\!\left(\left|\frac{n_k(T)}{N} - \frac{C_{k-1}}{4^{k-1}}\right| \ge \varepsilon\right) = 0.$$

---

## 7. Aldous's Fringe Law, Equidistribution, and Universality

Section 6 establishes concentration for the aggregate count $n_k(T)$ of all complete $k$-leaf sub-trees regardless of their internal topology. Fixing a concrete pattern tree $S \in \mathcal{T}_k$ refines this aggregate law to a single-shape ("fringe") theorem: every shape of arity $k$ appears with identical asymptotic density $4^{-(k-1)}$, concentrates around this limit, occurs almost surely in large random trees, and exhausts total probability mass $1$ across all finite shapes.

### 7.1 Single-Shape Support and Equidistribution

**Definition 7.1 (Single-Shape Support).**
Fix a pattern tree $S \in \mathcal{T}_k$ ($k \ge 2$). For $T \in \mathcal{T}_N$ and a contiguous interval $I = [i, i + k)$ inside $\{0, \dots, N - 1\}$ ($0 \le i$, $i + k \le N$), we say that $I$ supports a *complete sub-tree of shape $S$* in $T$ (written $I \triangleleft_S T$, `ShapeSupport`) if $I \triangleleft T$ and the sub-tree extracted at $I$ (`extractAt`) equals $S$. Let
$$n_S(T) := \#\{I \in \mathcal{I}_k(N) \mid I \triangleleft_S T\}$$
(`shapeCount`) denote the multiplicity of shape $S$ in $T$, so that $n_k(T) = \sum_{S \in \mathcal{T}_k} n_S(T)$.

**Theorem 7.2 (Single-Shape Operadic Factorization and Equidistribution).**
*For any fixed $2 \le k \le N$, contiguous interval $I = [i, i + k) \subseteq \{0, \dots, N - 1\}$, and pattern $S \in \mathcal{T}_k$:*
1. *Restricting the operadic bijection of Theorem 2.1 to the inner component $T_{\mathrm{in}} = S$ yields an explicit bijection (`operadicShapeEquiv`):*
   $$\mathcal{T}_{N - k + 1} \;\xrightarrow{\ \sim\ }\; \{ T \in \mathcal{T}_N \mid I \triangleleft_S T \}, \qquad T_{\mathrm{out}} \longmapsto T_{\mathrm{out}} \circ_i S.$$
   *In particular, the single-shape fiber cardinality is (`subtree_shape_fiber_card`):*
   $$\#\{T \in \mathcal{T}_N \mid I \triangleleft_S T\} = C_{N - k},$$
   *independent of both the position $i$ and the internal shape $S \in \mathcal{T}_k$.*
2. *Summing over all $N - k + 1$ contiguous intervals yields the global single-shape multiplicity (`globalShapeMultiplicity_eq`):*
   $$\Phi_S(N) := \sum_{T \in \mathcal{T}_N} n_S(T) = (N - k + 1) C_{N - k} = \binom{2(N - k)}{N - k},$$
   *and the exact expected single-shape density under the uniform measure on $\mathcal{T}_N$ is (`expectedShapeDensity_eq`):*
   $$\mathbb{E}[n_S](N) = \frac{\Phi_S(N)}{|\mathcal{T}_N|} = \frac{\binom{2(N - k)}{N - k}}{\frac{1}{N}\binom{2N - 2}{N - 1}} = \frac{\mathbb{E}[n_k](N)}{C_{k-1}}.$$
3. *As $N \to \infty$ for fixed $k \ge 2$, every shape $S \in \mathcal{T}_k$ occurs at equal asymptotic frequency $q_k := 4^{-(k-1)}$:*
   $$\mathbb{E}[n_S](N) = \frac{1}{4^{k-1}}\,N + \frac{k - 1}{2 \cdot 4^{k-1}} + \mathcal{O}\!\left(\frac{1}{N}\right) = \frac{1}{4^{k-1}}\,N + \mathcal{O}(1).$$

*Proof.*
Grafting $S$ at leaf $i$ of $T_{\mathrm{out}} \in \mathcal{T}_{N-k+1}$ produces a tree whose sub-tree spanning $[i, i + k)$ is $S$ itself, and conversely the inverse of Theorem 2.1 extracts $S$ as the second coordinate whenever $I \triangleleft_S T$. Hence `operadicShapeEquiv` restricts to a bijection with $\mathcal{T}_{N-k+1}$, of cardinality $C_{N-k}$. Summing over $i \in \{0, \dots, N - k\}$ gives $\Phi_S(N) = (N - k + 1) C_{N-k} = \binom{2(N-k)}{N-k}$. Dividing by $C_{N-1} = \frac{1}{N}\binom{2N-2}{N-1}$ yields $\mathbb{E}[n_S](N) = \mathbb{E}[n_k](N)/C_{k-1}$, so dividing Theorem 5.2 by $C_{k-1}$ gives the exact asymptotic expansion. $\blacksquare$

### 7.2 Single-Shape Variance, Concentration, and Finite-Pattern Universality

**Theorem 7.3 (Single-Shape Second Moment and Linear Variance Scaling).**
*Fix $k \ge 2$ and $S \in \mathcal{T}_k$, and set $q_k := 4^{-(k-1)}$.*
1. *For disjoint intervals $I = [i, i+k)$ and $J = [j, j+k)$ ($i + k \le j$, $j + k \le N$), restricting Theorem 6.1 to $S_I = S_J = S$ gives an explicit bijection (`operadicShapeTwoSiteEquiv`):*
   $$\mathcal{T}_{N - 2k + 2} \;\xrightarrow{\ \sim\ }\; \{ T \in \mathcal{T}_N \mid I \triangleleft_S T \text{ and } J \triangleleft_S T \},$$
   *with joint fiber cardinality $C_{N - 2k + 1}$ (`shape_two_site_fiber_card`, `shape_disjoint_fiber_card`).*
2. *The global second factorial multiplicity $\Phi_{2,S}(N) := \sum_{T \in \mathcal{T}_N} n_S(T)\big(n_S(T) - 1\big)$ satisfies:*
   $$\Phi_{2,S}(N) = \begin{cases} 0 & \text{if } N < 2k, \\ (N - 2k + 1)\dbinom{2(N - 2k + 1)}{N - 2k + 1} & \text{if } N \ge 2k, \end{cases}$$
   *so $\Phi_{2,S}(N) = \Phi_2(N, k) / C_{k-1}^2$.*
3. *The variance $\mathrm{Var}(n_S)(N) := \mathbb{E}[n_S^2](N) - \mathbb{E}[n_S](N)^2$ satisfies the linear scaling law (`shapeVariance_sub_linear_tendsto`, `shapeVariance_div_tendsto`, `shapeVariance_asymptotic`):*
   $$\mathrm{Var}(n_S)(N) = \left(\frac{1}{4^{k-1}} - \frac{2k - 1}{16^{k-1}}\right) N + \mathcal{O}(1) \qquad (N \to \infty),$$
   *with strictly positive slope $q_k - (2k - 1) q_k^2 > 0$ for all $k \ge 2$ (`shapeVariance_slope_pos`).*

*Proof.*
Double-counting ordered pairs of disjoint $k$-intervals inside $\{0, \dots, N - 1\}$ exactly as in Theorem 6.2 yields $\Phi_{2,S}(N)$ and $\Phi_2(N, k) = C_{k-1}^2 \Phi_{2,S}(N)$. Expanding $\mathbb{E}[n_S^2] = \frac{\Phi_{2,S}(N)}{C_{N-1}} + \mathbb{E}[n_S](N)$ alongside $\mathbb{E}[n_k^2] = \frac{\Phi_2(N,k)}{C_{N-1}} + \mathbb{E}[n_k](N)$ gives the exact identity
$$\mathrm{Var}(n_S)(N) = \frac{\mathrm{Var}(n_k)(N) - \mathbb{E}[n_k](N)}{C_{k-1}^2} + \mathbb{E}[n_S](N).$$
Substituting the linear expansions of Theorems 5.2, 6.4, and 7.2, the $N^2$ terms cancel and the coefficient of $N$ is
$$\frac{(p_k - (2k - 1) p_k^2) - p_k}{C_{k-1}^2} + q_k = q_k - (2k - 1) q_k^2,$$
since $p_k = C_{k-1} q_k$. Finally, an elementary induction on $k \ge 2$ shows $2k - 1 < 4^{k-1}$ (at $k = 2$, $3 < 4$; if $2k - 1 < 4^{k-1}$, then $2(k + 1) - 1 = (2k - 1) + 2 < 4 \cdot 4^{k-1} = 4^k$), so $q_k - (2k - 1) q_k^2 = \frac{4^{k-1} - (2k - 1)}{16^{k-1}} > 0$. $\blacksquare$

**Theorem 7.4 (Aldous Fringe Concentration and Finite-Pattern Universality).**
*For every fixed $k \ge 2$, every pattern $S \in \mathcal{T}_k$, and every $\varepsilon > 0$:*
1. *(Chebyshev Concentration, `shapeDensity_concentration_bound`, `shapeDensity_concentration_tendsto`)*
   $$\mathbb{P}_{T \in \mathcal{T}_N}\!\left(\left|\frac{n_S(T)}{N} - \frac{1}{4^{k-1}}\right| \ge \varepsilon\right) \le \frac{\mathrm{Var}(n_S)(N) + \big(\mathbb{E}[n_S](N) - q_k N\big)^2}{\varepsilon^2 N^2} \xrightarrow{\ N \to \infty\ } 0.$$
2. *(Finite-Pattern Universality, `shape_universality_tendsto`) Every fixed finite binary tree $S \in \mathcal{T}_k$ occurs at least once in a uniformly random $N$-leaf binary tree with probability tending to $1$:*
   $$\lim_{N \to \infty} \mathbb{P}_{T \in \mathcal{T}_N}\big(n_S(T) \ge 1\big) = 1.$$

*Proof.*
Part (1) follows from Chebyshev's inequality applied to $n_S(T)$ centered at $q_k N$, since $\mathrm{Var}(n_S)(N) = \mathcal{O}(N)$ and $\mathbb{E}[n_S](N) - q_k N = \mathcal{O}(1)$ by Theorems 7.2 and 7.3. For (2), set $\varepsilon = q_k = 4^{-(k-1)} > 0$. Whenever $n_S(T) = 0$, we have $|n_S(T)/N - q_k| = q_k \ge \varepsilon$; hence
$$\mathbb{P}_{T \in \mathcal{T}_N}\big(n_S(T) = 0\big) \le \mathbb{P}_{T \in \mathcal{T}_N}\!\left(\left|\frac{n_S(T)}{N} - q_k\right| \ge q_k\right) \xrightarrow{\ N \to \infty\ } 0,$$
and taking complements yields $\mathbb{P}_{T \in \mathcal{T}_N}(n_S(T) \ge 1) = 1 - \mathbb{P}_{T \in \mathcal{T}_N}(n_S(T) = 0) \to 1$. $\blacksquare$

### 7.3 Fringe Mass Normalization

**Theorem 7.5 (Fringe Mass Normalization).**
*The Catalan fringe weights $p_k = \frac{C_{k-1}}{4^{k-1}}$ ($k \ge 2$) sum to $1$ (`fringeMass_partialSum_tendsto`):*
$$\lim_{M \to \infty} \sum_{k=2}^{M - 1} \frac{C_{k-1}}{4^{k-1}} = 1 \qquad \text{(equivalently, } \sum_{k=2}^{\infty} \sum_{S \in \mathcal{T}_k} \frac{1}{4^{k-1}} = 1\text{)}.$$
*Consequently, the single-shape asymptotic frequencies $\{4^{-(k-1)} : k \ge 2,\ S \in \mathcal{T}_k\}$ form a genuine probability measure on the countable set of all finite full binary trees, with zero mass escaping to infinity.*

*Proof.*
Define the telescoping remainder $r_n := \frac{(2n + 1) C_n}{4^n}$ for $n \ge 0$, noting $r_0 = 1$. By the Catalan recurrence $(n + 2) C_{n+1} = 2(2n + 1) C_n$, we have
$$r_n - r_{n+1} = \frac{(2n + 1) C_n}{4^n} - \frac{(2n + 3) C_{n+1}}{4^{n+1}} = \frac{2(n + 2) C_{n+1} - (2n + 3) C_{n+1}}{4^{n+1}} = \frac{C_{n+1}}{4^{n+1}}.$$
Telescoping over $n = 0, \dots, M - 3$ (with $k = n + 2 \in [2, M)$ for $M \ge 2$) gives the exact identity
$$\sum_{k=2}^{M-1} \frac{C_{k-1}}{4^{k-1}} = r_0 - r_{M-2} = 1 - r_{M-2}.$$
To show $r_n \to 0$, let $b_n := \frac{1}{4^n}\binom{2n}{n}$. From $b_0 = 1$ and $b_{n+1} = \frac{2n+1}{2(n+1)} b_n$, induction gives $(2n + 1) b_n^2 \le 1$ for all $n \ge 0$, because $(2n + 3)\big(\frac{2n+1}{2n+2}\big)^2 \le 2n + 1$. Since $r_n = \frac{2n+1}{n+1} b_n \le 2 b_n$, we obtain
$$0 \le r_n^2 \le 4 b_n^2 \le \frac{4}{2n + 1} \xrightarrow{\ n \to \infty\ } 0,$$
so $r_{M-2} \to 0$ and the partial sums converge to $1$. $\blacksquare$

---

## 8. Boundary Tower $K_N \hookrightarrow K_{N+1}$ and $K_\infty$ Scaling Geometry

Having analyzed the asymptotic sub-tree distribution on $\mathcal{T}_N$, we now connect consecutive associahedra via boundary facet inclusions $K_N \hookrightarrow K_{N+1}$ and compare the exponential growth of the $1$-skeleton against the quadratic height of the Tamari lattice.

### 8.1 Inductive Boundary Facet Embeddings ($K_N \hookrightarrow K_{N+1}$)

At the maximal proper arity $k = N$ ($N \ge 2$), the outer quotient tree has arity $(N + 1) - N + 1 = 2$, and $\mathcal{T}_2$ consists of the unique $2$-leaf tree `rootTwo` ($\wedge$). Specializing Theorem 2.1 at $(N + 1, k = N, i = 0)$ and $(N + 1, k = N, i = 1)$ yields two canonical tree-level boundary embeddings (`boundaryEmbed`, `boundaryEmbedRight`):
$$\iota_N : \mathcal{T}_N \hookrightarrow \mathcal{T}_{N+1}, \quad T \longmapsto (T \wedge \bullet), \qquad \iota_N^{\mathrm{R}} : \mathcal{T}_N \hookrightarrow \mathcal{T}_{N+1}, \quad T \longmapsto (\bullet \wedge T),$$
with exact image (`boundaryEmbed_range`, `boundaryEmbedEquiv`):
$$\mathrm{im}(\iota_N) = \{ T \in \mathcal{T}_{N+1} \mid [0, N) \triangleleft T \}.$$

Geometrically, by Theorem 4.0.2 of [thin-category-lattice.md](thin-category-lattice.md#L213), the boundary diagonal $[0, N)$ (`boundaryFacetDiagonal`) cuts out a facet $F_{[0, N)} \cong K_N \times K_2$ of $K_{N+1}$. Because $K_2$ is a single point (`Unique (LodayExposedFace 0)`), projecting away the trivial factor produces a canonical order isomorphism of face posets (`boundaryFacet_orderIso_self`):
$$F_{[0, N)}(K_{N+1}) \;\cong\; K_N \times K_2 \;\cong\; K_N,$$
and hence an order-embedding of exposed face posets $\partial_N : \mathcal{F}(K_N) \hookrightarrow \mathcal{F}(K_{N+1})$ (`boundaryFaceEmbed`) lying below $F_{[0, N)}$ (`boundaryFaceEmbed_le_boundaryFacet`).

**Proposition 8.1 (Compatibility Along the Tower).**
*For every $N \ge 2$, the left boundary embedding $\iota_N : \mathcal{T}_N \hookrightarrow \mathcal{T}_{N+1}$:*
1. *Preserves all sub-tree supports $[i, i + k) \subseteq [0, N)$ (`boundaryEmbed_preserves_subtreeSupport`), and maps onto the Loday boundary facet $F_{[0, N)}$ (`boundaryEmbed_on_loday_boundaryFacet`, `loday_vertex_on_boundaryFacet_iff`);*
2. *Preserves vertex–facet incidence with every proper Loday facet of $K_N$ (`boundaryEmbed_preserves_loday_facet_incidence`), acting on Loday coordinates by preserving the first $N - 1$ coordinates and appending the root gap weight $N$ (`boundaryEmbed_lodayPoint_castSucc`, `boundaryEmbed_lodayPoint_last`).*

*Composing $m$ steps yields the iterated vertex and face-poset embeddings (`iteratedBoundaryEmbed`, `iteratedFaceEmbed`):*
$$\iota_{N, m} : \mathcal{T}_N \hookrightarrow \mathcal{T}_{N+m}, \qquad \partial_{N, m} : \mathcal{F}(K_N) \hookrightarrow \mathcal{F}(K_{N+m}),$$
*which define the directed boundary tower $K_2 \hookrightarrow K_3 \hookrightarrow \cdots \hookrightarrow K_N \hookrightarrow K_{N+1} \hookrightarrow \cdots \to K_\infty$ preserving all sub-tree supports (`iteratedBoundaryEmbed_preserves_subtreeSupport`) and face inclusions (`iteratedFaceEmbed_le_iff`).*

### 8.2 $(N - 2)$-Regularity and Edge Count of $K_N$

Every full binary tree $T \in \mathcal{T}_N$ ($N \ge 2$) has $N - 1$ internal nodes: one root node spanning $[0, N)$ and $N - 2$ proper internal nodes spanning proper intervals $[a, b)$ with $2 \le b - a \le N - 1$ (`properInternalSpans_card`). Rotating across each proper internal node produces a distinct neighbor in the $1$-skeleton of $K_N$.

**Theorem 8.2 (Associahedron $(N - 2)$-Regularity and Edge Count).**
*For every $N \ge 2$, let $\mathrm{Sk}_1(K_N)$ (`tamariGraph`) denote the simple graph on $\mathcal{T}_N$ whose edges are single tree rotations (`RotationStep`). Then:*
1. *$\mathrm{Sk}_1(K_N)$ is $(N - 2)$-regular (`tamariGraph_degree`):*
   $$\deg_{K_N}(T) = |\mathrm{properInternalSpans}(T)| = N - 2 \qquad (\forall T \in \mathcal{T}_N),$$
   *where each proper internal span corresponds to an adjacent vertex sharing a $1$-dimensional Loday edge of $K_N$ (`properInternalSpan_rotation_edge`).*
2. *The total number of edges of $K_N$ (`associahedronEdgeCount`, `tamariGraph_edgeCount`, `two_mul_associahedronEdgeCount`) is:*
   $$|\mathrm{Edge}(K_N)| = \frac{N - 2}{2}\,C_{N - 1} = \frac{N - 2}{2N}\binom{2N - 2}{N - 1}.$$

*Proof.*
By structural induction on $T$, `rotationNeighbors T` partitions into disjoint sets from the left subtree, right subtree, root right-rotation, and root left-rotation, of total cardinality $N - 2$ (`rotationNeighbors_card`), matching the $N - 2$ proper internal spans (`properInternalSpans_card`). Summing degrees over all $|\mathcal{T}_N| = C_{N-1}$ vertices and applying the handshaking lemma gives $2 |\mathrm{Edge}(K_N)| = (N - 2) C_{N-1}$ (`two_mul_associahedronEdgeCount_eq_sum`), where $(N - 2) C_{N-1}$ is always even (`two_dvd_degree_mul_catalan`) because either $2 \mid (N - 2)$ (for even $N$) or $N$ is odd and $2 \mid N C_{N-1} = \binom{2N-2}{N-1}$. $\blacksquare$

### 8.3 Exponential Horizontal Expansion vs. Quadratic Tamari Height

While the degree $N - 2$ grows linearly and the Tamari poset height grows at most quadratically, the horizontal edge count of $K_N$ grows exponentially at rate $4^{N-1}$.

**Theorem 8.3 (Exponential Edge Expansion vs. Quadratic Tamari Height).**
1. *(Exponential Horizontal Growth, `log_edgeCount_div_tendsto`) From the central binomial bounds $\frac{4^m}{2m + 1} \le \binom{2m}{m} \le 4^m$ (`centralBinom_le_four_pow`, `four_pow_le_mul_centralBinom`), for all $N \ge 3$ we have*
   $$\frac{N - 2}{2(2N - 1) N}\,4^{N - 1} \;\le\; |\mathrm{Edge}(K_N)| \;\le\; 4^{N - 1},$$
   *and hence*
   $$\lim_{N \to \infty} \frac{\log |\mathrm{Edge}(K_N)|}{(N - 1)\log 4} = 1.$$
2. *(Quadratic Tamari Height Bound, `tamari_chain_length_le`) Let $\le_{\mathrm{Tam}}$ (`TamariLE`) be the reflexive-transitive closure of right rotations (`tamariPartialOrder`). Any strictly increasing chain $T_0 <_{\mathrm{Tam}} T_1 <_{\mathrm{Tam}} \dots <_{\mathrm{Tam}} T_L$ in $(\mathcal{T}_N, \le_{\mathrm{Tam}})$ (in particular, any maximal chain between $\bot$ and $\top$) has length bounded by:*
   $$L \le \frac{(N - 1)(N - 2)}{2} \le \binom{N}{2} = \frac{N(N - 1)}{2}.$$
3. *(Height-to-Edge Collapse, `quadratic_height_div_edgeCount_tendsto`) Consequently, the ratio of maximum chain height to total edge count decays exponentially to zero:*
   $$\lim_{N \to \infty} \frac{\binom{N}{2}}{|\mathrm{Edge}(K_N)|} = 0.$$

*Proof.*
For (1), taking logarithms of the upper and lower bounds on $|\mathrm{Edge}(K_N)|$ gives
$$1 - \frac{\log(8N)}{(N - 1)\log 4} \le \frac{\log |\mathrm{Edge}(K_N)|}{(N - 1)\log 4} \le 1$$
for $N \ge 4$, and $\frac{\log N}{N} \to 0$ squeezes the ratio to $1$. For (2), define the left-edge potential $\Phi_L(T)$ (`leftEdgeCount`) recursively on internal nodes by $\Phi_L(A \wedge B) := (|A| - 1) + \Phi_L(A) + \Phi_L(B)$, where $|A|$ is the leaf count of $A$. Every single right rotation $(A \wedge B) \wedge C \to A \wedge (B \wedge C)$ strictly decreases $\Phi_L$ by $|A| \ge 1$ (`RightRotation.leftEdgeCount_lt`), which simultaneously proves antisymmetry of $\le_{\mathrm{Tam}}$ and forces $L \le \Phi_L(T_0)$ along any strict chain of length $L$. Structural induction gives $\Phi_L(T) \le \frac{(N - 1)(N - 2)}{2} \le \binom{N}{2}$ (`leftEdgeCount_le`, `leftEdgeCount_le_choose_two`). For (3), the lower bound $|\mathrm{Edge}(K_N)| \ge \frac{4^N}{32 N}$ ($N \ge 4$) yields $\binom{N}{2}/|\mathrm{Edge}(K_N)| \le 16 N^3 / 4^N \to 0$. $\blacksquare$

*Finite-$N$ Scaling Snapshot:* At $K_{13}$ ($N = 13$), $|\mathcal{T}_{13}| = C_{12} = 208{,}012$ vertices of degree $11$ span $|\mathrm{Edge}(K_{13})| = 1{,}144{,}066$ edges, giving log-edge fill $\frac{\log |\mathrm{Edge}(K_{13})|}{12\log 4} \approx 83.86\%$ and degree fraction $\frac{N - 2}{N} = \frac{11}{13} \approx 84.62\%$, while Tamari chains have length at most $\binom{12}{2} = 66 \le \binom{13}{2} = 78$ ($\binom{13}{2}/|\mathrm{Edge}(K_{13})| \approx 6.82 \times 10^{-5}$). One step higher at $K_{14}$ ($N = 14$), $|\mathcal{T}_{14}| = C_{13} = 742{,}900$ vertices of degree $12$ span $|\mathrm{Edge}(K_{14})| = 4{,}457{,}400$ edges, with log-edge fill $\approx 84.95\%$ and $\frac{12}{14} \approx 85.71\%$ versus height bound $\binom{14}{2} = 91$ ($\binom{14}{2}/|\mathrm{Edge}(K_{14})| \approx 2.04 \times 10^{-5}$). Thus $K_\infty$ grows exponentially wide ($\sim 4^{N-1}$) while remaining quadratically shallow ($\mathcal{O}(N^2)$).

---

## 9. Lean 4 Formalization and Machine Verification

All results above are formalized without `sorry` placeholders in Lean 4 (`v4.35.0`, Mathlib) and depend solely on the standard core axioms `[propext, Classical.choice, Quot.sound]`:

* **Core subtree embeddings, variance & concentration:** [`AssociahedralSubtreeEmbeddings.lean`](math_project/MathProject/AssociahedralSubtreeEmbeddings.lean)
* **Single-shape fringe laws & universality:** [`AssociahedralFringeLaw.lean`](math_project/MathProject/AssociahedralFringeLaw.lean)
* **Boundary tower, regularity & $K_\infty$ growth:** [`AssociahedralBoundaryTower.lean`](math_project/MathProject/AssociahedralBoundaryTower.lean)
* **Axiom audit & small-case checks:** [`CheckSubtreeEmbeddings.lean`](math_project/MathProject/CheckSubtreeEmbeddings.lean)

| Paper Statement | Mathematical Concept | Lean 4 Declaration |
| :--- | :--- | :--- |
| **Definition 1.1** | Sub-tree support, proper-interval bridge to `PartialBracketing N`, Loday vertex–facet incidence, and $F_I \cong K_k \times K_{N-k+1}$ | `SubtreeSupport`, `subtreeSupport_iff_mem_partialBracketing`, `subtreeSupport_iff_loday_vertex_on_facet`, `subtreeFacet_product_orderIso` |
| **Theorem 2.1** | Explicit grafting/extraction bijection $\mathcal{T}_{N-k+1} \times \mathcal{T}_k \simeq \{T \in \mathcal{T}_N \mid I \triangleleft T\}$ and fiber cardinality $C_{k-1} C_{N-k}$ | `graftTree`, `extractAt`, `contractAt`, `operadicFactorizationEquiv`, `subtree_fiber_card` |
| **Theorem 3.1** | Double counting across intervals and trees; Loday vertex–facet incidence sum; global multiplicity $\Phi(N, k) = C_{k-1}\binom{2(N-k)}{N-k}$ | `globalSubtreeMultiplicity`, `globalSubtreeMultiplicity_eq_tree_sum`, `globalSubtreeMultiplicity_eq_loday_incidence`, `globalSubtreeMultiplicity_eq` |
| **Corollary 4.1** | Minimal binary generators ($k = 2$): $\Phi(N, 2) = \binom{2N-4}{N-2}$ | `globalSubtreeMultiplicity_k2` |
| **Theorem 5.1** | Average over trees, `MeasureTheory.Measure.uniformOfFinset` expectation form, and exact closed-form density $\mathbb{E}[n_k](N)$ | `expectedSubtreeDensity`, `expectedSubtreeDensity_eq_tree_avg`, `expectedSubtreeDensity_eq_uniform_expectation`, `expectedSubtreeDensity_eq` |
| **Theorem 5.2** | Limit $\mathbb{E}[n_k](N) - \frac{C_{k-1}}{4^{k-1}} N \to \frac{C_{k-1}(k-1)}{2 \cdot 4^{k-1}}$, $+\,\mathcal{O}(1)$ bound, and exact $+\,\mathcal{O}(1/N)$ remainder bound | `expectedSubtreeDensity_sub_linear_tendsto`, `expectedSubtreeDensity_asymptotic`, `expectedSubtreeDensity_asymptotic_inv` |
| **Theorem 6.1** | Two-site operadic bijection $\mathcal{T}_{N-2k+2} \times \mathcal{T}_k \times \mathcal{T}_k \simeq \{T \in \mathcal{T}_N \mid I \triangleleft T \land J \triangleleft T\}$ and joint fiber cardinality $C_{k-1}^2 C_{N-2k+1}$ | `operadicTwoSiteEquiv`, `subtree_two_site_fiber_card`, `subtree_disjoint_fiber_card` |
| **Theorem 6.2** | Global pair multiplicity $\Phi_2(N, k)$ vanishing for $N < 2k$ and closed form for $N \ge 2k$ | `globalSubtreePairMultiplicity`, `globalSubtreePairMultiplicity_eq_zero_of_lt`, `globalSubtreePairMultiplicity_eq` |
| **Proposition 6.3** | Exact second moment $\mathbb{E}[n_k^2](N)$ and exact cherry variance $\mathrm{Var}(n_2)(N)$ for $N \ge 3$ | `subtreeSecondMoment`, `subtreeSecondMoment_eq`, `subtreeVariance`, `subtreeVariance_k2` |
| **Theorem 6.4** | Positive slope $p_k - (2k - 1) p_k^2 > 0$, convergent $\mathrm{Var}(n_k)(N) - s N \to C$, $\mathrm{Var}(n_k)(N)/N \to s$, and $\mathrm{Var}(n_k)(N) = \mathcal{O}(N)$ | `varianceSlope_pos`, `subtreeVariance_sub_linear_tendsto`, `subtreeVariance_div_tendsto`, `subtreeVariance_asymptotic` |
| **Theorem 6.5** | Finite-$N$ Chebyshev concentration inequality and convergence $\mathbb{P}(|n_k(T)/N - p_k| \ge \varepsilon) \to 0$ under `Measure.uniformOfFinset` | `subtreeDensity_concentration_bound`, `subtreeDensity_concentration_tendsto` |
| **Definition 7.1 & Theorem 7.2** | Single-shape support $I \triangleleft_S T$, operadic equivalence $\mathcal{T}_{N-k+1} \simeq \{T \in \mathcal{T}_N \mid I \triangleleft_S T\}$, fiber size $C_{N-k}$, $\Phi_S(N) = \binom{2(N-k)}{N-k}$, and $\mathbb{E}[n_S](N) = 4^{-(k-1)}N + \mathcal{O}(1)$ | `ShapeSupport`, `operadicShapeEquiv`, `subtree_shape_fiber_card`, `shapeCount`, `globalShapeMultiplicity`, `globalShapeMultiplicity_eq_tree_sum`, `globalShapeMultiplicity_eq`, `expectedShapeDensity`, `expectedShapeDensity_eq`, `expectedShapeDensity_sub_linear_tendsto`, `expectedShapeDensity_asymptotic`, `expectedShapeDensity_asymptotic_inv` |
| **Theorem 7.3** | Two-site single-shape factorization, pair multiplicity $\Phi_{2,S}(N)$, positive slope $4^{-(k-1)} - (2k-1)16^{-(k-1)} > 0$, and linear variance $\mathrm{Var}(n_S)(N) = \mathcal{O}(N)$ | `operadicShapeTwoSiteEquiv`, `shape_two_site_fiber_card`, `shape_disjoint_fiber_card`, `globalShapePairMultiplicity`, `globalShapePairMultiplicity_eq_zero_of_lt`, `globalShapePairMultiplicity_eq`, `shapeSecondMoment`, `shapeSecondMoment_eq`, `shapeVariance`, `shapeVariance_eq_uniform_expectation`, `shapeVariance_slope_pos`, `shapeVariance_sub_linear_tendsto`, `shapeVariance_div_tendsto`, `shapeVariance_asymptotic` |
| **Theorem 7.4** | Single-shape Chebyshev bound, concentration $n_S(T)/N \xrightarrow{\mathbb{P}} 4^{-(k-1)}$, and Finite-Pattern Universality $\mathbb{P}(n_S(T) \ge 1) \to 1$ | `shapeDensity_concentration_bound`, `shapeDensity_concentration_tendsto`, `shape_universality_tendsto` |
| **Theorem 7.5** | Fringe mass normalization $\sum_{k=2}^{M-1} C_{k-1}/4^{k-1} \to 1$ | `fringeMass_partialSum_tendsto` |
| **Proposition 8.1** | Boundary embeddings $K_N \cong K_N \times K_2 \hookrightarrow K_{N+1}$, Loday facet & coordinate preservation, and iterated tower $K_N \hookrightarrow K_{N+m}$ | `rootTwo`, `boundaryEmbed`, `boundaryEmbedRight`, `boundaryEmbed_range`, `boundaryEmbedEquiv`, `boundaryEmbed_preserves_subtreeSupport`, `boundaryFacetDiagonal`, `boundaryEmbed_on_loday_boundaryFacet`, `loday_vertex_on_boundaryFacet_iff`, `boundaryEmbed_preserves_loday_facet_incidence`, `boundaryFacet_orderIso_self`, `boundaryFaceEmbed`, `iteratedBoundaryEmbed`, `iteratedFaceEmbed` |
| **Theorem 8.2** | $(N - 2)$-regularity of the Tamari rotation graph `tamariGraph N` and edge count $|\mathrm{Edge}(K_N)| = \frac{N-2}{2} C_{N-1}$ | `properInternalSpans`, `properInternalSpans_card`, `properInternalSpans_total_sum`, `two_dvd_degree_mul_catalan`, `associahedronEdgeCount`, `two_mul_associahedronEdgeCount`, `two_mul_associahedronEdgeCount_eq_sum`, `rotationNeighbors_card`, `tamariGraph`, `tamariGraph_degree`, `tamariGraph_edgeCount`, `properInternalSpan_rotation_edge` |
| **Theorem 8.3** | Exponential horizontal growth $\frac{\log|\mathrm{Edge}(K_N)|}{(N-1)\log 4} \to 1$, quadratic Tamari chain bound $\binom{N}{2}$, and $\binom{N}{2}/|\mathrm{Edge}(K_N)| \to 0$ | `centralBinom_le_four_pow`, `four_pow_le_mul_centralBinom`, `associahedronEdgeCount_le_four_pow`, `four_pow_le_associahedronEdgeCount_mul`, `log_edgeCount_div_tendsto`, `leftEdgeCount`, `RightRotation.leftEdgeCount_lt`, `TamariLE`, `tamariPartialOrder`, `tamari_chain_length_le`, `quadratic_height_div_edgeCount_tendsto` |

Verified with:
```bash
lake build MathProject.AssociahedralSubtreeEmbeddings MathProject.AssociahedralFringeLaw MathProject.AssociahedralBoundaryTower MathProject.CheckSubtreeEmbeddings
```
