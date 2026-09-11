/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Authors: Shivansh Singh
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.Order.Field

/-!
# OntologicalFriction

This module implements OntologicalFriction.
-/

set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

open Filter Topology

namespace OntologicalFriction

variable {U : Type} [Fintype U]
variable (cl : Set U → Set U)

/-- A set is a generating set if its closure covers the universe. -/
def IsGeneratingSet (S : Set U) : Prop :=
  cl S = Set.univ

/-- An optimal generating set minimizes cardinality. -/
def IsOptimalGenerator (S : Set U) : Prop :=
  IsGeneratingSet cl S ∧ ∀ T, IsGeneratingSet cl T → S.toFinite.toFinset.card ≤ T.toFinite.toFinset.card

/-- The approximation ratio (Friction 1) compares the sieve's output to the optimal size. -/
noncomputable def cardinalityBloat (sieve_output : Set U) (opt : Set U) 
    (_h_opt : IsOptimalGenerator cl opt) : ℚ :=
  (sieve_output.toFinite.toFinset.card : ℚ) / (opt.toFinite.toFinset.card : ℚ)

/-- Search Work (Friction 2) represents the discard rate W. -/
noncomputable def searchWork (k : ℕ) (sieve_output : Set U) : ℚ :=
  let b_omega := sieve_output.toFinite.toFinset.card
  if k = 0 then (0 : ℚ) else ((k - b_omega : ℕ) : ℚ) / (k : ℚ)

theorem searchWork_perfect_alignment (k : ℕ) (sieve_output : Set U)
    (h : sieve_output.toFinite.toFinset.card = k) :
    searchWork k sieve_output = 0 := by
  dsimp [searchWork]
  rw [h]
  split_ifs with hk
  · rfl
  · rw [Nat.sub_self, Nat.cast_zero, zero_div]

theorem searchWork_limit (sieve_output : Set U) :
    Tendsto (fun (k : ℕ) => searchWork k sieve_output) atTop (𝓝 1) := by
  let b_omega := sieve_output.toFinite.toFinset.card
  have h_eq : (fun (k : ℕ) => searchWork k sieve_output) =ᶠ[atTop] (fun (k : ℕ) => 1 - (b_omega : ℚ) * ((k : ℚ)⁻¹)) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use b_omega + 1
    intro k hk
    dsimp [searchWork]
    have hk0 : k ≠ 0 := by omega
    rw [if_neg hk0]
    have h_sub : (k - b_omega : ℕ) = (k : ℚ) - (b_omega : ℚ) := by
      exact Nat.cast_sub (by omega)
    rw [h_sub, div_eq_mul_inv, sub_mul]
    have hk_q : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
    have hk_mul_inv : (k : ℚ) * (k : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hk_q
    rw [hk_mul_inv]
  refine Tendsto.congr' h_eq.symm ?_
  have h_inv : Tendsto (fun (k : ℕ) => ((k : ℚ)⁻¹)) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h_mul : Tendsto (fun (k : ℕ) => (b_omega : ℚ) * ((k : ℚ)⁻¹)) atTop (𝓝 0) := by
    have h_zero : (b_omega : ℚ) * 0 = 0 := mul_zero _
    rw [← h_zero]
    exact Tendsto.const_mul (b_omega : ℚ) h_inv
  have h_one : Tendsto (fun (k : ℕ) => (1 : ℚ)) atTop (𝓝 1) := tendsto_const_nhds
  have h_sub : Tendsto (fun (k : ℕ) => 1 - (b_omega : ℚ) * ((k : ℚ)⁻¹)) atTop (𝓝 (1 - 0)) :=
    Tendsto.sub h_one h_mul
  rw [sub_zero] at h_sub
  exact h_sub

end OntologicalFriction
