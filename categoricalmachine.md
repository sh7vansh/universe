# The categorical ontological sieve: transfinite cellular decomposition in abelian categories

This note specifies a transfinite cellular filtration for objects in Grothendieck categories. For any semi-Artinian object, the construction extracts simple subobjects from successive cokernels using pullbacks, records the Yoneda extension classes at each stage, and reconstructs the object as a directed colimit of an extension tower.

---

## 1. Ambient categorical foundations

The construction takes place in a Grothendieck category $\mathcal{A}$, which is an abelian category satisfying Grothendieck's AB5 axiom (cocomplete, with a generator and exact filtered colimits).

In $\mathcal{A}$, every monomorphism is a kernel and every epimorphism is a cokernel:

$$
m = \ker(\mathrm{coker} m), \quad e = \mathrm{coker}(\ker e)
$$

Every morphism $f: X \to Y$ factors through an exact sequence:

$$
0 \to \ker(f) \to X \twoheadrightarrow \mathrm{im}(f) \hookrightarrow Y \to \mathrm{coker}(f) \to 0
$$

with $\mathrm{coim}(f) \cong \mathrm{im}(f)$.

Because filtered colimits commute with finite limits (axiom AB5), the filtered colimit of an ascending chain of monomorphisms $m_\alpha: C_\alpha \hookrightarrow U_0$ is a monomorphism $\varinjlim C_\alpha \hookrightarrow U_0$. The colimit can therefore be identified with a subobject of $U_0$.

### Ambient objects and residual cokernels

Fix an ambient object $U_0 \in \mathrm{Ob}(\mathcal{A})$. A subobject of $U_0$ is an equivalence class of monomorphisms $m: C \hookrightarrow U_0$.

For any subobject $C \hookrightarrow U_0$, the residual object is the canonical cokernel:

$$
0 \to C \xrightarrow{m} U_0 \xrightarrow{q_C} S_C \to 0, \quad S_C = \mathrm{coker}(m)
$$

When $C \cong U_0$, the quotient is zero: $S_{U_0} \cong 0$.

### The semi-Artinian condition

An object $a \in \mathrm{Ob}(\mathcal{A})$ is simple if $a \not\cong 0$ and its only subobjects are $0$ and $a$. The socle of an object $X$, written $\mathrm{Soc}(X)$, is the sum of all simple subobjects of $X$.

We assume that $U_0$ is semi-Artinian (also called a Loewy object). Every non-zero quotient object $S$ of $U_0$ has an essential socle:

$$
S \not\cong 0 \implies \mathrm{Soc}(S) \neq 0
$$

If $\mathrm{Soc}(S) = 0$, as occurs with $\mathbb{Z}$ in $\mathbf{Ab}$ or $\mathcal{O}_X$ in $\mathrm{Coh}(X)$ when $\dim X \ge 1$, the quotient has no simple subobjects and the construction cannot proceed. The semi-Artinian condition is necessary and sufficient to ensure that non-zero residual quotients always contain simple subobjects. For objects with zero socle, one instead uses the dual filtration by simple quotients $S \twoheadrightarrow a$ and radical co-filtrations.

---

## 2. The cellular step

Rather than choosing points from a set, each step extracts a simple subobject from the residual quotient.

```
                           0
                           |
                           v
                     C_alpha ---------------------> C_alpha
                           |                           |
                           | (kernel)                  | (pullback mono)
                           v                           v
0 --------> C_alpha ----> C_{alpha+1} -------------> U_0 ------------> S_{alpha+1} ----> 0
                           |                           |                   ^
                           | (pullback epi)            | q_alpha           |
                           v                           v                   |
0 ---------------------> a_{alpha+1} --------------> S_alpha -------------> S_{alpha+1} ----> 0
                                     i_{alpha+1}
```

### The selection map

Let $\mathrm{Res}(U_0) = \{S_C \mid C \hookrightarrow U_0, S_C \not\cong 0\}$ be the set of non-zero quotients. A selection map $\Phi$ assigns to each residual quotient $S_C$ a simple subobject:

$$
\Phi(S_C) = (a \xrightarrow{i_a} S_C), \quad a \text{ simple in } \mathcal{A}
$$

Because $U_0$ is semi-Artinian, $\mathrm{Soc}(S_C) \neq 0$, so $\Phi(S_C)$ is always well-defined.

### Pullback expansion and short exact sequences

Given the stage subobject $C_\alpha \hookrightarrow U_0$ with projection $q_\alpha: U_0 \twoheadrightarrow S_\alpha$, let $i_{\alpha+1}: a_{\alpha+1} \hookrightarrow S_\alpha$ be the simple subobject chosen by $\Phi(S_\alpha)$.

The next stage $C_{\alpha+1} \hookrightarrow U_0$ is the pullback in $\mathcal{A}$ of $i_{\alpha+1}$ along $q_\alpha$:

$$
\begin{array}{ccc}
C_{\alpha+1} & \xrightarrow{m_{\alpha+1}} & U_0 \\
\pi_{\alpha+1} \Big\downarrow & & \Big\downarrow q_\alpha \\
a_{\alpha+1} & \xrightarrow{i_{\alpha+1}} & S_\alpha
\end{array}
$$

In an abelian category, pullbacks preserve several exact properties:
1. Monomorphisms pull back to monomorphisms, so $m_{\alpha+1}: C_{\alpha+1} \hookrightarrow U_0$ is monic.
2. Epimorphisms pull back to epimorphisms, so $\pi_{\alpha+1}: C_{\alpha+1} \twoheadrightarrow a_{\alpha+1}$ is epic.
3. For any arrow $x: X \to C_{\alpha+1}$, $\pi_{\alpha+1} \circ x = 0$ if and only if $q_\alpha \circ (m_{\alpha+1} \circ x) = 0$. By the universal property of kernels, this factors uniquely through $\ker(q_\alpha) \cong C_\alpha$. Thus:

   $$
   \ker(\pi_{\alpha+1}) \cong C_\alpha
   $$

4. Every epimorphism in $\mathcal{A}$ is the cokernel of its kernel, giving the exact sequence:

   $$
   0 \to C_\alpha \hookrightarrow C_{\alpha+1} \xrightarrow{\pi_{\alpha+1}} a_{\alpha+1} \to 0
   $$

   This establishes that $C_{\alpha+1} / C_\alpha \cong a_{\alpha+1}$.

---

## 3. Transfinite recursion

The filtration proceeds by transfinite recursion over the ordinals.

```
                  +-----------------------------------+
                  |   Initialize:                     |
                  |     alpha = 0, C_0 = 0            |
                  |     A_0 = {}, Xi_0 = {}           |
                  +-----------------+-----------------+
                                    |
                                    v
                         +--------------------+
                         |   S_alpha == 0?    |
                         +---------+----------+
                                   |
                          No       |        Yes
                +------------------+------------------+
                |                                     |
                v                                     v
+---------------------------------+   +----------------------------------+
| Residual S_alpha = coker(C_a)   |   | Terminate: Omega = alpha         |
| Simple layer:                   |   | Reconstruct U_0 via colimit:     |
|   a_{alpha+1} = Phi(S_alpha)    |   |   U_0 = colim C_alpha            |
| Pullback to C_{alpha+1}:        |   +----------------------------------+
|   0 -> C_a -> C_{a+1} -> a -> 0 |
| Record extension class:         |
|   xi_{alpha+1} in Ext^1(a, C_a) |
+---------------+-----------------+
                |
                v
+---------------------------------+
| Limit step:                     |
|   C_lambda = colim_{beta} C_beta|
+---------------+-----------------+
                |
                +---> (Loop back)
```

### Recursion steps

1. **Initialization.**
   Set $\alpha = 0$, $C_0 = 0$, $\mathcal{A}_0 = \emptyset$ (the sequence of simple layers), and $\Xi_0 = \emptyset$ (the sequence of extension classes).

2. **Successor step ($\alpha \to \alpha + 1$).**
   Form $S_\alpha = \mathrm{coker}(C_\alpha \hookrightarrow U_0)$.
   If $S_\alpha \cong 0$, the ambient object is exhausted. Set $\Omega = \alpha$ and stop.
   Otherwise:
   * Select a simple subobject $i_{\alpha+1}: a_{\alpha+1} \hookrightarrow S_\alpha$ via $\Phi(S_\alpha)$.
   * Form the pullback $C_{\alpha+1} = U_0 \times_{S_\alpha} a_{\alpha+1}$, which yields:

     $$
     0 \to C_\alpha \to C_{\alpha+1} \to a_{\alpha+1} \to 0
     $$

   * Record the classifying Yoneda extension class:

     $$
     \xi_{\alpha+1} \in \mathrm{Ext}^1_{\mathcal{A}}(a_{\alpha+1}, C_\alpha)
     $$

   * Update the sequences: $\mathcal{A}_{\alpha+1} = \mathcal{A}_\alpha \cup \{a_{\alpha+1}\}$ and $\Xi_{\alpha+1} = \Xi_\alpha \cup \{\xi_{\alpha+1}\}$.

3. **Limit step ($\lambda$ a limit ordinal).**
   Take the directed colimit of the chain in $\mathcal{A}$:

   $$
   C_\lambda = \varinjlim_{\beta < \lambda} C_\beta, \quad \mathcal{A}_\lambda = \bigcup_{\beta < \lambda} \mathcal{A}_\beta, \quad \Xi_\lambda = \bigcup_{\beta < \lambda} \Xi_\beta
   $$

   By axiom AB5, the canonical arrow $C_\lambda \hookrightarrow U_0$ is a monomorphism.

---

## 4. Convergence and vanishing of residual colimits

### Convergence theorems

> **Theorem 1 (Convergence for finite-length objects).** Let $U_0 \in \mathrm{Ob}(\mathcal{A})$ have finite length (both Artinian and Noetherian). The recursion terminates at a finite ordinal $\Omega < \omega$ with $C_\Omega \cong U_0$. The integer $\Omega = \ell(U_0)$ equals the Jordan-Hölder length of $U_0$.

*Proof.* In an object of finite length, every strictly ascending chain of subobjects terminates in finitely many steps $\Omega \le \ell(U_0) < \omega$. Because $a_{\alpha+1}$ is simple, $a_{\alpha+1} \not\cong 0$, so each inclusion $C_\alpha \subsetneq C_{\alpha+1}$ is strict. Every quotient of a finite-length object has a non-zero socle, so the construction cannot stall before $S_\Omega = 0$. Thus $C_\Omega \cong U_0$. $\blacksquare$

> **Theorem 2 (Transfinite convergence for semi-Artinian objects).** Let $U_0$ be a semi-Artinian object. The recursion terminates at an ordinal $\Omega \le \mathrm{loewy}(U_0) \cdot |U_0|^+$ with $C_\Omega \cong U_0$.

*Proof.* By the semi-Artinian hypothesis, whenever $C_\alpha \subsetneq U_0$, the quotient $S_\alpha = U_0 / C_\alpha$ has $\mathrm{Soc}(S_\alpha) \neq 0$. The selection map $\Phi(S_\alpha)$ is always non-empty, so $\{C_\alpha\}$ is strictly increasing. In a Grothendieck category, the subobjects of $U_0$ form a small complete lattice. A strictly increasing transfinite chain cannot exceed the successor cardinal of this lattice, so it must stabilize at some ordinal $\Omega$ where $S_\Omega \cong 0$, forcing $C_\Omega \cong U_0$. $\blacksquare$

### Vanishing of the residual colimit

> **Theorem 3 (Vanishing of the residual colimit).** Let $\{S_\alpha\}_{\alpha < \Omega}$ be the diagram of residual cokernels with canonical projections $q_{\beta, \alpha}: S_\alpha \twoheadrightarrow S_\beta$ for $\alpha \le \beta$. The directed colimit of this diagram vanishes:
>
> $$
> \varinjlim_{\alpha < \Omega} S_\alpha \cong 0
> $$

*Proof.* Colimits commute with colimits. Because cokernels are colimits:

$$
\varinjlim_{\alpha < \Omega} S_\alpha \cong \varinjlim_{\alpha < \Omega} \mathrm{coker}(C_\alpha \hookrightarrow U_0) \cong \mathrm{coker}\left(\varinjlim_{\alpha < \Omega} C_\alpha \hookrightarrow U_0\right)
$$

By axiom AB5, the filtered colimit of the monomorphisms $C_\alpha \hookrightarrow U_0$ is a monomorphism $\varinjlim C_\alpha \hookrightarrow U_0$. By Theorems 1 and 2, $\varinjlim_{\alpha < \Omega} C_\alpha \cong C_\Omega \cong U_0$. Therefore:

$$
\varinjlim_{\alpha < \Omega} S_\alpha \cong \mathrm{coker}(\mathrm{id}_{U_0}: U_0 \to U_0) \cong 0
$$

$\blacksquare$

---

## 5. Reconstruction

The ambient object $U_0$ is recovered as the directed colimit of its stages:

$$
U_0 \cong \varinjlim_{\alpha < \Omega} C_\alpha
$$

Rebuilding $U_0$ from the simple layers $\{a_\alpha\}$ depends on whether extensions split in $\mathcal{A}$.

### Semisimple categories

When $\mathcal{A}$ is semisimple (for instance, finite group representations over $\mathbb{C}$ or vector spaces), all short exact sequences split, so $\mathrm{Ext}^1(a, C) = 0$.

Every step splits:

$$
C_{\alpha+1} \cong C_\alpha \oplus a_{\alpha+1}
$$

Because colimits commute with coproducts, $U_0$ is the direct sum of its simple layers:

$$
U_0 \cong \bigoplus_{\alpha < \Omega} a_{\alpha+1}
$$

### Categories with non-trivial extensions

When $\mathrm{Ext}^1 \neq 0$, an object cannot be determined from its composition factors alone. For example, $\mathbb{Z}/p^2\mathbb{Z}$ and $\mathbb{Z}/p\mathbb{Z} \oplus \mathbb{Z}/p\mathbb{Z}$ share identical simple factors but are not isomorphic.

Here, $U_0$ is reconstructed from the recorded sequence of simple layers and extension classes $(\mathcal{A}_\Omega, \Xi_\Omega)$:
1. Set $C_0 = 0$.
2. For each successor ordinal, $C_{\alpha+1}$ is the extension:

   $$
   0 \to C_\alpha \to C_{\alpha+1} \to a_{\alpha+1} \to 0
   $$

   classified by $\xi_{\alpha+1} \in \mathrm{Ext}^1_{\mathcal{A}}(a_{\alpha+1}, C_\alpha)$.
3. For limit ordinals, $C_\lambda = \varinjlim_{\beta < \lambda} C_\beta$.
4. $U_0 \cong C_\Omega$.

The pair $(\mathcal{A}_\Omega, \Xi_\Omega)$ determines $U_0$ up to isomorphism.

---

## 6. Additive invariants and the Grothendieck group

Because filtered colimits allow infinite coproducts, the Grothendieck group of the full category $\mathcal{A}$ collapses to zero by the Eilenberg swindle ($M \oplus M^\infty \cong M^\infty$, which forces $[M] = 0$).

To obtain non-trivial invariants, we restrict to the Serre subcategory of finite-length objects, $\mathcal{A}_{\text{fl}} \subseteq \mathcal{A}$.

The Grothendieck group $K_0(\mathcal{A}_{\text{fl}})$ is the free abelian group on isomorphism classes $[X]$ of finite-length objects, modulo $[B] = [A] + [C]$ for each short exact sequence $0 \to A \to B \to C \to 0$.

Because each step forms a short exact sequence $0 \to C_\alpha \to C_{\alpha+1} \to a_{\alpha+1} \to 0$, the classes satisfy:

$$
[C_{\alpha+1}] = [C_\alpha] + [a_{\alpha+1}]
$$

When $U_0$ has finite length, the termination ordinal is finite ($\Omega < \omega$), and the class of $U_0$ decomposes as:

$$
[U_0] = \sum_{\alpha=0}^{\Omega-1} [a_{\alpha+1}]
$$

### Jordan-Hölder invariance

By the Jordan-Hölder theorem in $\mathcal{A}_{\text{fl}}$, the multiset of simple composition factors $\{a_1, \dots, a_\Omega\}$ is an invariant of $U_0$, independent of the choice map $\Phi$.

Any additive invariant, such as module length $\ell$ or vector space dimension, factors through $K_0(\mathcal{A}_{\text{fl}})$ as a homomorphism $V: K_0(\mathcal{A}_{\text{fl}}) \to \mathbb{R}$. The step-wise difference is strictly positive:

$$
\Delta V_\alpha = V(C_{\alpha+1}) - V(C_\alpha) = V(a_{\alpha+1}) > 0
$$

---

## 7. Concrete categories and examples

### Finite abelian groups and torsion modules

In the category $\mathbf{Ab} = \mathbb{Z}\text{-}\mathbf{Mod}$, let $U_0$ be a finite abelian group $\bigoplus_{i} \mathbb{Z}/p_i^{k_i}\mathbb{Z}$, or a torsion group such as the Prüfer group $\mathbb{Z}(p^\infty)$.

The simple objects are cyclic groups of prime order $\mathbb{Z}/p\mathbb{Z}$. Each quotient $S_\alpha = U_0 / C_\alpha$ has a non-zero socle containing prime-order cyclic submodules. The construction extracts the prime composition series.

For torsion-free groups such as $\mathbb{Z}$, $\mathrm{Soc}(\mathbb{Z}) = 0$. The subobject filtration cannot run on $\mathbb{Z}$ directly; such objects require the dual filtration using simple quotients $\mathbb{Z} \twoheadrightarrow \mathbb{Z}/p\mathbb{Z}$.

### Representations of acyclic quivers

Let $\mathrm{Rep}_k(Q)$ be the category of representations of a finite acyclic quiver $Q$ over a field $k$, and let $V$ be a finite-dimensional representation.

The simple objects are one-dimensional representations $S_i$ at each vertex $i \in Q_0$. In an acyclic quiver, every non-zero finite-dimensional representation has a non-zero socle of vertex simples. The construction extracts these vertex simples, and the recorded classes $\xi_\alpha \in \mathrm{Ext}^1(S_i, C_\alpha)$ reconstruct the indecomposable components of the representation.

### Representations of finite groups

Let $\mathcal{A} = \mathbb{C}[G]\text{-}\mathbf{Mod}$ for a finite group $G$, with $U_0 = \mathbb{C}[G]$ the regular representation.

The simple objects are the irreducible representations $V_\lambda$. By Maschke's theorem, $\mathbb{C}[G]$ is semisimple, so all short exact sequences split ($\mathrm{Ext}^1 = 0$). The filtration decomposes the regular representation directly into a direct sum of irreps:

$$
\mathbb{C}[G] \cong \bigoplus_{\lambda \in \widehat{G}} V_\lambda^{\oplus \dim V_\lambda}
$$

### Zero-dimensional coherent sheaves

Let $\mathrm{QCoh}(X)$ be the category of quasi-coherent sheaves on an algebraic variety $X$. Let $\mathcal{F} \in \mathrm{Coh}_0(X)$ be a coherent torsion sheaf supported on a finite zero-dimensional subscheme.

The simple objects are skyscraper sheaves $k(x)$ supported at closed points $x \in X$. Every non-zero zero-dimensional sheaf has an essential socle of skyscraper sheaves. The construction extracts the points of support sequentially.

The dimension of global sections $\dim_k H^0(X, \mathcal{F})$ is an additive invariant on $K_0(\mathrm{Coh}_0(X))$, tracking the length at each step. By contrast, positive-dimensional sheaves such as $\mathcal{O}_X$ have $\mathrm{Soc}(\mathcal{O}_X) = 0$, requiring the dual quotient filtration.

---

## 8. Summary

| Component | Categorical specification |
| :--- | :--- |
| Ambient category | Grothendieck category $\mathcal{A}$ (abelian, AB5) |
| Regularity condition | Semi-Artinian object $U_0$: $\mathrm{Soc}(U_0 / C) \neq 0$ for all $C \subsetneq U_0$ |
| Residual map | Cokernel: $0 \to C_\alpha \to U_0 \xrightarrow{q_\alpha} S_\alpha \to 0$ |
| Generator choice | Simple subobject: $i_{\alpha+1}: a_{\alpha+1} \hookrightarrow S_\alpha$ from $\mathrm{Soc}(S_\alpha)$ |
| Stage expansion | Pullback $C_{\alpha+1} = U_0 \times_{S_\alpha} a_{\alpha+1}$, yielding $0 \to C_\alpha \to C_{\alpha+1} \to a_{\alpha+1} \to 0$ |
| Termination | Vanishing colimit: $\varinjlim S_\alpha \cong \mathrm{coker}(\varinjlim C_\alpha \to U_0) \cong 0$ |
| Reconstruction | Colimit $U_0 \cong \varinjlim C_\alpha$ via extension data $(\mathcal{A}_\Omega, \Xi_\Omega)$ with $\xi \in \mathrm{Ext}^1$ |
| Additive invariants | On $\mathcal{A}_{\text{fl}}$: Grothendieck group $K_0(\mathcal{A}_{\text{fl}})$, Jordan-Hölder factors, length $\Delta V = V(a) > 0$ |

## Lean 4 Formalization

The structural properties of the categorical sieve, such as exact sequences and subobjects in an abelian category, can be formalized using Mathlib's category theory library.

```lean
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Subobject.Lattice

namespace CategoricalMachine

open CategoryTheory
open CategoryTheory.Limits

-- Let A be an abelian category
variable {A : Type*} [Category A] [Abelian A]

/-- A simple object has exactly two subobjects: 0 and itself. -/
def IsSimple (X : A) : Prop :=
  ¬ IsZero X ∧ ∀ (Y : Subobject X), Y = ⊥ ∨ Y = ⊤

variable (U₀ : A)

/-- The residual object is the cokernel of a subobject inclusion. -/
noncomputable def residual (C : Subobject U₀) : A :=
  cokernel C.arrow

/-- The semi-Artinian condition: every non-zero quotient has a simple subobject. -/
def IsSemiArtinian (U₀ : A) : Prop :=
  ∀ (C : Subobject U₀), ¬ IsZero (residual U₀ C) → 
    ∃ (a : A) (i : a ⟶ residual U₀ C), IsSimple a ∧ Mono i

/-- The cellular step forms a pullback of the simple subobject along the quotient map. -/
noncomputable def cellularStep 
    (C : Subobject U₀) 
    (a : A) 
    (i : a ⟶ residual U₀ C) [Mono i] : A :=
  pullback i (cokernel.π C.arrow)

/-- The canonical morphism from the cellular step into the ambient object. -/
noncomputable def cellularStepArrow
    (C : Subobject U₀) 
    (a : A) 
    (i : a ⟶ residual U₀ C) [Mono i] : cellularStep U₀ C a i ⟶ U₀ :=
  pullback.snd i (cokernel.π C.arrow)

/-- Because pullbacks preserve monomorphisms, the new cellular step is a valid subobject of U₀. -/
instance cellularStep_is_mono 
    (C : Subobject U₀) 
    (a : A) 
    (i : a ⟶ residual U₀ C) [Mono i] : Mono (cellularStepArrow U₀ C a i) := by
  dsimp [cellularStepArrow]
  exact pullback.snd_of_mono

/-- The subobject corresponding to the cellular step. -/
noncomputable def cellularSubobject
    (C : Subobject U₀) 
    (a : A) 
    (i : a ⟶ residual U₀ C) [Mono i] : Subobject U₀ :=
  Subobject.mk (cellularStepArrow U₀ C a i)

end CategoricalMachine
```

### Transfinite Colimits and Convergence

The heavy transfinite limit proofs and convergence mappings are modeled over filtered ordinal categories in their own dedicated module:

**Theorem 3: Vanishing Residual Colimit**
If the transfinite recursion converges to the top subobject $U_0$ at some limit ordinal $\Omega$, then the directed colimit of the residual diagram maps exactly to the zero object:
```lean
theorem residual_colimit_vanishes (F : J ⥤ Subobject U₀) [IsFiltered J] 
    (h_conv : Convergence U₀ F) :
    IsZero (colimit (residualDiagram U₀ F))
```
[See full proof in CategoricalColimits.lean](file:///home/shivansh/math_project/MathProject/CategoricalColimits.lean)
