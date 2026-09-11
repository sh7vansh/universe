/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Authors: Shivansh Singh
-/
import Mathlib.Order.Closure
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic

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

/-- A Discovery Operator selects a new element outside the current closed set. -/
def DiscoveryOperator (U : Type) := 
  ∀ (C : Set U), C ⊂ Set.univ → U

section FixedPriority

variable [LinearOrder U] [WellFoundedLT U]

noncomputable def fixedPriorityPhi : DiscoveryOperator U :=
  fun C h =>
    let compl : Set U := Cᶜ
    have h_nonempty : compl.Nonempty := Set.nonempty_compl.mpr h.ne
    WellFounded.min wellFounded_lt compl h_nonempty

theorem novelty_of_fixedPriorityPhi (C : Set U) (h : C ⊂ Set.univ) :
    fixedPriorityPhi C h ∉ C := by
  have h1 := WellFounded.min_mem wellFounded_lt Cᶜ (Set.nonempty_compl.mpr h.ne)
  exact h1

end FixedPriority

section AdaptiveGreedy

variable [Fintype U]

noncomputable def adaptiveGreedyPhi (cl : Set U → Set U) : DiscoveryOperator U :=
  fun C h =>
    let compl := Cᶜ
    have h_nonempty : compl.Nonempty := Set.nonempty_compl.mpr h.ne
    have h_exists : ∃ x ∈ compl, ∀ y ∈ compl, 
        (cl (C ∪ {y})).toFinite.toFinset.card ≤ (cl (C ∪ {x})).toFinite.toFinset.card := by
      let f := fun (y : U) => (cl (C ∪ {y})).toFinite.toFinset.card
      have h_fin : compl.Finite := Set.toFinite compl
      have h_finset_nonempty : h_fin.toFinset.Nonempty := by
        exact h_fin.toFinset_nonempty.mpr h_nonempty
      rcases Finset.exists_max_image h_fin.toFinset f h_finset_nonempty with ⟨x, hx, hmax⟩
      use x
      rw [Set.Finite.mem_toFinset] at hx
      use hx
      intro y hy
      have hy_finset : y ∈ h_fin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact hy
      exact hmax y hy_finset
    Classical.choose h_exists

end AdaptiveGreedy

open Classical

noncomputable def B_seq (cl : Set U → Set U) (phi : DiscoveryOperator U) (o : Ordinal) : Set U :=
  Ordinal.limitRecOn o
    (∅ : Set U)
    (fun _ B => if h : cl B ⊂ Set.univ then B ∪ {phi (cl B) h} else B)
    (fun a _ f => ⋃ (b : Ordinal) (hb : b < a), f b hb)

noncomputable def sieve_output (cl : Set U → Set U) (phi : DiscoveryOperator U) : Set U :=
  ⋃ o : Ordinal.{0}, B_seq cl phi o

end OntologicalMachine
