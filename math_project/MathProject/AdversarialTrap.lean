/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shivansh Singh
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import MathProject.OntologicalMachine
import MathProject.OntologicalFriction
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Instances.Rat

/-!
# AdversarialTrap

This module implements AdversarialTrap.
-/

set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

open Classical
open OntologicalMachine
open OntologicalFriction
open Filter Topology

namespace AdversarialTrap

variable {U : Type} (e_star : U)

noncomputable def advCl (S : Set U) : Set U :=
  if e_star ∈ S then Set.univ else S

instance : ClosureSystem (advCl e_star) where
  extensive X := by
    dsimp [advCl]
    split_ifs
    · exact Set.subset_univ X
    · exact Set.Subset.rfl
  monotone X Y hXY := by
    dsimp [advCl]
    split_ifs with hX hY
    · exact Set.Subset.rfl
    · exact False.elim (hY (hXY hX))
    · exact Set.subset_univ X
    · exact hXY
  idempotent X := by
    dsimp [advCl]
    split_ifs with hX hUniv
    · rfl
    · exact False.elim (hUniv (Set.mem_univ e_star))
    · rfl

theorem gen_e_star : advCl e_star {e_star} = Set.univ := by
  dsimp [advCl]
  have h : e_star ∈ ({e_star} : Set U) := Set.mem_singleton e_star
  rw [if_pos h]

theorem optimal_e_star [Fintype U] :
    IsOptimalGenerator (advCl e_star) {e_star} := by
  constructor
  · exact gen_e_star e_star
  · intro T hT
    dsimp [IsGeneratingSet] at hT
    have h1 : ({e_star} : Set U).toFinite.toFinset.card = 1 := by simp
    rw [h1]
    by_cases hEmpty : T = ∅
    · have hCl : advCl e_star T = ∅ := by
        rw [hEmpty]
        dsimp [advCl]
        rw [if_neg (by simp)]
      rw [hCl] at hT
      have h_in_univ : e_star ∈ (Set.univ : Set U) := Set.mem_univ e_star
      rw [←hT] at h_in_univ
      exact False.elim (by simp at h_in_univ)
    · have hNonEmpty : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
      have hFinsetNonEmpty : T.toFinite.toFinset.Nonempty := by simp [hNonEmpty]
      exact Finset.card_pos.mpr hFinsetNonEmpty

variable [Fintype U]

theorem searchWork_adv_trap_limit :
    Tendsto (fun k => searchWork k ({e_star} : Set U)) atTop (𝓝 1) := by
  exact OntologicalFriction.searchWork_limit {e_star}

end AdversarialTrap
