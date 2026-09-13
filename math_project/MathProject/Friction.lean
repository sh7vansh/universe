/-
Copyright (c) 2024 MathProject. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algorithmic Friction
-/
import Mathlib.Order.Cover
import Mathlib.Order.Atoms
import Mathlib.Order.CompleteLattice.Basic

/-!
# Algorithmic Friction in Lattice Theory
-/

set_option linter.style.header false
set_option linter.style.longLine false

variable {L : Type*} [CompleteLattice L]

/-- The Mac Lane-Steinitz Exchange Property -/
def MacLaneSteinitz : Prop :=
  ∀ a b x : L, IsAtom a → IsAtom b → a ≤ x ⊔ b → ¬(a ≤ x) → b ≤ x ⊔ a

/-- Geometric Friction is the absence of the Mac Lane-Steinitz Exchange Property -/
def GeometricFriction : Prop :=
  ¬ @MacLaneSteinitz L _

/-- Semimodular property via the covering relation -/
def Semimodular : Prop :=
  ∀ x y : L, x ⊓ y ⋖ x → y ⋖ x ⊔ y

/-- Semimodular Friction is the absence of Semimodularity -/
def SemimodularFriction : Prop :=
  ¬ @Semimodular L _

/-- The rank collapse tautology:
    Because the algorithm output and optimal generator both span the entire lattice (⊤),
    any rank comparison between them reduces to a structural tautology. -/
theorem rank_collapse (r : L → ℕ) (alg_out opt_gen : L) (h_alg : alg_out = ⊤) (h_opt : opt_gen = ⊤) :
    r alg_out = r opt_gen := by
  rw [h_alg, h_opt]

