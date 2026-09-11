# The ontological sieve: greedy generator extraction in closure systems

## The construction

Take a set $U$ and a closure operator $\mathrm{cl}: \mathcal{P}(U) \to \mathcal{P}(U)$ that is extensive ($X \subseteq \mathrm{cl}(X)$), monotonic ($X \subseteq Y \implies \mathrm{cl}(X) \subseteq \mathrm{cl}(Y)$), and idempotent ($\mathrm{cl}(\mathrm{cl}(X)) = \mathrm{cl}(X)$).

To pull a generating set out of $U$, we need a choice rule. Fix a total well-order $\prec$ on $U$. This well-order can come from a priority function or pre-order, with ties broken arbitrarily.

Define the discovery operator $\Phi$ on closed subsets $C \subsetneq U$:

$$
\Phi(C) = \min_{\prec}(U \setminus C)
$$

The extraction runs by transfinite induction:
1. Start with $B_0 = \emptyset$ and $C_0 = \mathrm{cl}(\emptyset)$.
2. At step $\alpha + 1$, if $U \subseteq C_\alpha$, stop and set $\Omega = \alpha$. Otherwise, pick $p_{\alpha+1} = \Phi(C_\alpha)$, set $B_{\alpha+1} = B_\alpha \cup \{p_{\alpha+1}\}$, and close it: $C_{\alpha+1} = \mathrm{cl}(B_{\alpha+1})$.
3. At limit ordinals $\lambda$, set $B_\lambda = \bigcup_{\beta < \lambda} B_\beta$ and $C_\lambda = \mathrm{cl}(B_\lambda)$.

Because each step adds an element outside the current closure, the chain of closed sets strictly grows until it covers $U$. The process halts at an ordinal $\Omega < |U|^+$, leaving $C_\Omega = \mathrm{cl}(U)$ and generating family $B_\Omega$.

## Independence and failure modes

Every element chosen by $\Phi$ is outside the closure of earlier elements:

$$
p_{\alpha+1} \notin \mathrm{cl}(\{p_\beta \mid \beta \le \alpha\})
$$

This stagewise independence does not guarantee that the final set $B_\Omega$ is minimal or independent.

### Matroids

If $\mathrm{cl}$ has finite character and satisfies the Steinitz exchange property ($y \in \mathrm{cl}(X \cup \{x\}) \setminus \mathrm{cl}(X) \implies x \in \mathrm{cl}(X \cup \{y\})$), $(U, \mathrm{cl})$ is a matroid. Here, greedy selection works cleanly. Every maximal independent set has the same cardinality, and $B_\Omega$ is an independent basis. The order $\prec$ changes which basis you find, but not its size.

### Non-matroidal spaces

Without the exchange property, greedy selection with a fixed order is brittle. An adversary can arrange $\prec$ so that the algorithm picks many redundant elements before hitting a single element that generates the entire space.

This creates two distinct penalties:
* Cardinality bloat: $|B_\Omega| / |B_{\mathrm{OPT}}|$ can grow as large as $|U|$.
* Search waste: If the algorithm evaluates $k$ candidates to pick $|B_\Omega|$ generators, the discard rate $W = (k - |B_\Omega|) / k$ approaches 1 whenever the priority order puts strong generators at the end.

### Tracking novelty with Möbius inversion

When the poset of closed subsets is locally finite, you can measure how much new structure each generator introduces. For an observable $G$ defined on the lattice of closed sets, the Möbius inversion gives a layer-by-layer delta:

$$
\widehat{G}(X) = \sum_{Y \subseteq X} \mu(Y, X) G(Y)
$$

In the divisibility lattice of integers, applying this inversion to $G(n) = \log n$ recovers the von Mangoldt function $\Lambda(n)$, which is non-zero only on prime powers.

## Behavior across domains

The construction behaves differently depending on how well the well-order aligns with the closure rules.

### Quantum states

Let $U$ be a Hilbert space, $\mathrm{cl}$ the closed linear span, and order states by energy level. Because linear span satisfies the exchange property, the closure system is a matroid. Greedily taking the lowest-energy state outside the current span produces an orthonormal eigenbasis with zero discarded selections ($W = 0$).

### Formal logic

Let $U$ be the set of well-formed formulas, $\mathrm{cl}$ deductive closure, and order formulas by character length. Deductive closure fails the exchange property ($A \vdash B$ does not imply $B \vdash A$). The sieve tests thousands of short tautologies that are already implied by earlier selections. The discard rate is near 1, and the resulting axiom set depends heavily on the syntactic tie-breaking rule.

### Continuous geometry

Let $U = \mathbb{R}^n$, and let $\mathrm{cl}(X)$ be the orbit of $X$ under a continuous Lie group action. The orbits are dense and uncountable. A point-by-point well-order requires the Axiom of Choice to break ties, which decomposes the space into non-measurable sets instead of carving out a clean fundamental domain. To get a usable fundamental domain in continuous geometry, you have to work with open regions and quotient topologies rather than point-wise greedy selection.

### Arithmetic

Let $U = \mathbb{Z}_{\ge 2}$, and let closure be upward divisibility ($x \in \mathrm{cl}(S)$ if some $s \in S$ divides $x$). Ordering integers by standard magnitude ($2, 3, 4, \dots$) recovers the sieve of Eratosthenes. The primes emerge as the generating family, but the discard rate approaches 1 because composites vastly outnumber primes. The work happens because an additive order is being used to discover multiplicative structure. Ordering by divisibility directly turns primes into completely prime filters of the poset, eliminating the search waste.

## References

* Mac Lane, S. (1936). "Some Interpretations of Abstract Linear Dependence."
* Rota, G.-C. (1964). "Theory of Möbius Functions."
* Borodin, A., Nielsen, M. N., & Rackoff, C. (2003). (For the fixed-priority algorithm framework).

## Lean 4 Formalization

The basic structures of the ontological sieve can be expressed in Lean 4 as follows:

```lean
import Mathlib.Order.Closure
import Mathlib.Order.WellFounded

namespace OntologicalMachine

variable {U : Type}

/-- A closure operator satisfies extensivity, monotonicity, and idempotence. -/
class ClosureSystem (cl : Set U → Set U) where
  extensive : ∀ X, X ⊆ cl X
  monotone : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y
  idempotent : ∀ X, cl (cl X) = cl X

variable [LinearOrder U] [WellFoundedLT U]

noncomputable def Phi (C : Set U) (h : C ⊂ Set.univ) : U :=
  let compl : Set U := Cᶜ
  have h_nonempty : compl.Nonempty := Set.nonempty_compl.mpr h.ne
  WellFounded.min wellFounded_lt compl h_nonempty

theorem novelty_of_phi (C : Set U) (h : C ⊂ Set.univ) :
    Phi C h ∉ C := by
  have h1 := WellFounded.min_mem wellFounded_lt Cᶜ (Set.nonempty_compl.mpr h.ne)
  exact h1

end OntologicalMachine
```

[See full proof in OntologicalMachine.lean](https://raw.githubusercontent.com/sh7vansh/universe/refs/heads/main/math_project/MathProject/OntologicalMachine.lean)
