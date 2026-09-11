/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shivansh Singh
-/
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import MathProject.OntologicalMachine
import MathProject.OntologicalFriction

/-!
# MatroidFriction

This module implements MatroidFriction.
-/

set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

open Matroid OntologicalMachine

namespace OntologicalFriction

variable {U : Type}
variable (cl : Set U → Set U) [ClosureSystem cl]

/-- The Mac Lane-Steinitz exchange property for a closure operator. -/
def MacLaneSteinitz : Prop :=
  ∀ X x y, x ∉ cl X → x ∈ cl (insert y X) → y ∈ cl (insert x X)

/-- A Matroid whose ground set is the entire universe. -/
class UnivMatroid (M : Matroid U) : Prop where
  isUniv : M.E = Set.univ

/-- A universe-spanning Matroid naturally induces a ClosureSystem. -/
instance matroidClosureSystem (M : Matroid U) [UnivMatroid M] : ClosureSystem M.closure where
  extensive X := by
    have hX : X ⊆ M.E := by rw [UnivMatroid.isUniv]; exact Set.subset_univ X
    exact M.subset_closure X hX
  monotone X Y h := M.closure_subset_closure h
  idempotent X := M.closure_closure X

/-- A universe-spanning Matroid satisfies the Mac Lane-Steinitz exchange property. -/
lemma matroid_maclane (M : Matroid U) [UnivMatroid M] : MacLaneSteinitz M.closure := by
  intro X x y hnx hx_iny
  have h_diff : x ∈ M.closure (insert y X) \ M.closure X := ⟨hx_iny, hnx⟩
  have h_exc := M.closure_exchange h_diff
  exact h_exc.1

/-- An independent set in a closure system contains no redundant elements. -/
def IsIndependent (S : Set U) : Prop :=
  ∀ x ∈ S, x ∉ cl (S \ {x})

/-- The greedy Sieve yields a generating set with no redundant elements, under ANY priority order. -/
def IsGreedySieveOutput (S : Set U) : Prop :=
  IsGeneratingSet cl S ∧ IsIndependent cl S

set_option linter.unusedSectionVars false in
/-- 
Matroid Optimality Bound: 
If the closure system has the Mac Lane-Steinitz exchange property, 
the greedy Sieve yields a generating set of the exact same cardinality 
as the optimal basis (c=1). 
-/
theorem matroid_optimality_bound [Fintype U] [DecidableEq U]
    (M : Matroid U) [UnivMatroid M] (h_cl : cl = M.closure)
    (sieve_output : Set U) (h_sieve : IsGreedySieveOutput cl sieve_output)
    -- Note: sieve_output could be `OntologicalMachine.sieve_output cl Phi` for any Phi
    (opt : Set U) (h_opt : IsOptimalGenerator cl opt)
    (h_nz : opt.toFinite.toFinset.card ≠ 0) :
    cardinalityBloat cl sieve_output opt h_opt = 1 := by
  have h_subset : ∀ (X : Set U), X ⊆ M.E := fun X => by rw [UnivMatroid.isUniv]; exact Set.subset_univ X
  rcases h_sieve with ⟨h_sieve_gen, h_sieve_indep⟩
  rcases h_opt with ⟨h_opt_gen, h_opt_opt⟩
  have h_sieve_span : M.Spanning sieve_output := by
    rw [Matroid.spanning_iff_closure_eq (h_subset sieve_output), UnivMatroid.isUniv, ← h_cl]
    exact h_sieve_gen
  have h_sieve_indep_matroid : M.Indep sieve_output := by
    rw [Matroid.indep_iff_forall_notMem_closure_sdiff']
    refine ⟨h_subset sieve_output, ?_⟩
    intro e he
    have h1 := h_sieve_indep e he
    rwa [h_cl] at h1
  have h_sieve_base : M.IsBase sieve_output :=
    Matroid.Indep.isBase_of_spanning h_sieve_indep_matroid h_sieve_span
  have h_opt_span : M.Spanning opt := by
    rw [Matroid.spanning_iff_closure_eq (h_subset opt), UnivMatroid.isUniv, ← h_cl]
    exact h_opt_gen
  obtain ⟨B, hB_base, hB_sub⟩ := Matroid.Spanning.exists_isBase_subset h_opt_span
  have h_B_gen : cl B = Set.univ := by
    have hb_span : M.Spanning B := Matroid.IsBase.spanning hB_base
    rw [Matroid.spanning_iff_closure_eq (h_subset B), UnivMatroid.isUniv] at hb_span
    rwa [h_cl]
  have h_ncard := Matroid.IsBase.ncard_eq_ncard_of_isBase hB_base h_sieve_base
  have e1 : B.ncard = B.toFinite.toFinset.card := Set.ncard_eq_toFinset_card B B.toFinite
  have e2 : sieve_output.ncard = sieve_output.toFinite.toFinset.card := Set.ncard_eq_toFinset_card sieve_output sieve_output.toFinite
  rw [e1, e2] at h_ncard
  have h_card_eq : B.toFinite.toFinset.card = sieve_output.toFinite.toFinset.card := h_ncard
  have h_opt_le_B : opt.toFinite.toFinset.card ≤ B.toFinite.toFinset.card :=
    h_opt_opt B h_B_gen
  have h_B_le_opt : B.toFinite.toFinset.card ≤ opt.toFinite.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact hB_sub hx
  unfold cardinalityBloat
  have h_opt_eq_B : sieve_output.toFinite.toFinset.card = opt.toFinite.toFinset.card := by omega
  rw [h_opt_eq_B]
  have h_nz_Q : (opt.toFinite.toFinset.card : ℚ) ≠ 0 := by exact_mod_cast h_nz
  exact div_self h_nz_Q

end OntologicalFriction
