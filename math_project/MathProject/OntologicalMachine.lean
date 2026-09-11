/-
Copyright (c) 2024 MathProject Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathProject Authors
-/
import Mathlib.Order.Closure
import Mathlib.Order.WellFounded

/-!
# OntologicalMachine

This module implements OntologicalMachine.
-/

set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

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
