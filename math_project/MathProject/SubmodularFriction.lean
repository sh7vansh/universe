/-
Copyright (c) 2024 MathProject Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathProject Authors
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import MathProject.OntologicalFriction
import MathProject.OntologicalMachine
import MathProject.AdversarialTrap

/-!
# SubmodularFriction

This module formalizes the submodular approximation bound and the randomized expected bound
for the Ontological Sieve.
-/

set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.style.header false

open Real
open Classical

namespace OntologicalFriction

variable {U : Type} [Fintype U]

/-- A function is submodular if the marginal return is decreasing. -/
def IsSubmodular (f : Set U → ℝ) : Prop :=
  ∀ (A B : Set U) (x : U), A ⊆ B → x ∉ B →
    f (insert x A) - f A ≥ f (insert x B) - f B

/-- A rank function is a normalized, monotone submodular function. -/
structure RankFunction (U : Type) [Fintype U] where
  f : Set U → ℝ
  normalized : f ∅ = 0
  monotone : ∀ (A B : Set U), A ⊆ B → f A ≤ f B
  submodular : IsSubmodular f

/-- The rank function of a closure system. -/
noncomputable def closureRank (cl : Set U → Set U) (S : Set U) : ℝ :=
  (cl S).toFinite.toFinset.card

/-- Assumption that the closure operator yields a submodular rank function. -/
def IsSubmodularClosure (cl : Set U → Set U) : Prop :=
  IsSubmodular (closureRank cl)

/-- The maximum marginal gain of a single element (Δ). -/
noncomputable def maxMarginalGain (cl : Set U → Set U) : ℝ :=
  ↑(Finset.univ.sup (fun x => (cl {x}).toFinite.toFinset.card))

/-- The submodular approximation bound holds for the ADAPTIVE greedy sieve. -/
theorem greedy_submodular_bound [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl)
    (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl))
    (Δ : ℝ) (h_Δ : Δ = maxMarginalGain cl) :
    (greedy.toFinite.toFinset.card : ℝ) ≤ (Real.log Δ + 1) * (opt.toFinite.toFinset.card : ℝ) := by
  -- Proof blueprint:
  -- 1. Bound the marginal gain of each step by the remaining uncoverable rank.
  -- 2. Sum the discrete derivatives (telescoping sum).
  -- 3. Apply the harmonic number / log approximation bound.
  sorry

-- Lemmas for the adversarial trap
lemma advCl_max_marginal_gain (cl : Set U → Set U) (e_star : U) (h_cl : cl = fun S => if _h : e_star ∈ S then Set.univ else S) : 
    maxMarginalGain cl = Fintype.card U := by
  rw [maxMarginalGain]
  have h_sup : Finset.univ.sup (fun x => (cl {x}).toFinite.toFinset.card) = Fintype.card U := by
    apply le_antisymm
    · apply Finset.sup_le
      intro x hx
      exact Finset.card_le_univ _
    · have h_in : e_star ∈ (Finset.univ : Finset U) := Finset.mem_univ _
      have h_le := Finset.le_sup h_in (f := fun x => (cl {x}).toFinite.toFinset.card)
      have h_eval : (cl {e_star}).toFinite.toFinset.card = Fintype.card U := by
        have h_cl_estar : cl {e_star} = Set.univ := by
          rw [h_cl]
          have : e_star ∈ ({e_star} : Set U) := Set.mem_singleton e_star
          exact if_pos this
        rw [h_cl_estar]
        rw [Set.Finite.toFinset_univ, Finset.card_univ]
      rw [h_eval] at h_le
      exact h_le
  exact congrArg Nat.cast h_sup

lemma advCl_opt_size (cl : Set U → Set U) (opt : Set U) (e_star : U) (h_cl : cl = fun S => if _h : e_star ∈ S then Set.univ else S) (h_opt : IsOptimalGenerator cl opt) : 
    opt.toFinite.toFinset.card = 1 := by
  have h_adv : cl = AdversarialTrap.advCl e_star := by
    ext S
    rw [h_cl]
    rfl
  have h_e_star_opt : IsOptimalGenerator cl {e_star} := by
    rw [h_adv]
    exact AdversarialTrap.optimal_e_star e_star
  have h_le1 := h_opt.2 {e_star} h_e_star_opt.1
  have h_le2 := h_e_star_opt.2 opt h_opt.1
  have h_card : ({e_star} : Set U).toFinite.toFinset.card = 1 := by simp
  omega

lemma advCl_greedy_size_worst_case [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (greedy : Set U) (e_star : U) 
    (h_cl : cl = fun S => if _h : e_star ∈ S then Set.univ else S) 
    (h_worst : ∀ x, x ≤ e_star) -- e_star is the LAST element evaluated
    (h_greedy : greedy = OntologicalMachine.sieve_output cl OntologicalMachine.fixedPriorityPhi) : 
    greedy.toFinite.toFinset.card = Fintype.card U := by sorry

lemma log_bound_fails (n : ℝ) (hn : 3 ≤ n) : ¬ (n ≤ Real.log n + 1) := by
  have h1 : 0 < n := by linarith
  have h2 : n ≠ 1 := by linarith
  have h3 : Real.log n < n - 1 := Real.log_lt_sub_one_of_pos h1 h2
  intro h_false
  linarith

/-- The FIXED PRIORITY sieve violates the submodular bound.
    By using the adversarial trap, the fixed priority algorithm produces an output that scales as Θ(|U|),
    which explicitly breaks the ln(Δ) + 1 bound for sufficiently large U. -/
theorem fixed_priority_violates_submodular_bound [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (opt greedy : Set U) (e_star : U)
    (h_cl : cl = fun S => if _h : e_star ∈ S then Set.univ else S)
    (h_worst : ∀ x, x ≤ e_star)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl OntologicalMachine.fixedPriorityPhi)
    (h_opt : IsOptimalGenerator cl opt)
    (h_n : 3 ≤ Fintype.card U) :
    ¬ ( (greedy.toFinite.toFinset.card : ℝ) ≤ (Real.log (maxMarginalGain cl) + 1) * (opt.toFinite.toFinset.card : ℝ) ) := by
  -- 1. The maximum marginal gain is exactly |U|
  have h_gain : maxMarginalGain cl = Fintype.card U := advCl_max_marginal_gain cl e_star h_cl
  rw [h_gain]
  -- 2. The optimal generator is just {e_star}, size 1
  have h_opt_size : opt.toFinite.toFinset.card = 1 := advCl_opt_size cl opt e_star h_cl h_opt
  have h_opt_real : (opt.toFinite.toFinset.card : ℝ) = 1 := by exact_mod_cast h_opt_size
  rw [h_opt_real, mul_one]
  -- 3. The greedy algorithm evaluates e_star last, forcing it to pick every element, size |U|
  have h_greedy_size : greedy.toFinite.toFinset.card = Fintype.card U := advCl_greedy_size_worst_case cl greedy e_star h_cl h_worst h_is_greedy_output
  have h_greedy_real : (greedy.toFinite.toFinset.card : ℝ) = Fintype.card U := by exact_mod_cast h_greedy_size
  rw [h_greedy_real]
  -- 4. Apply the pure real inequality n > ln(n) + 1
  have h_n_real : 3 ≤ (Fintype.card U : ℝ) := by exact_mod_cast h_n
  exact log_bound_fails (Fintype.card U : ℝ) h_n_real

/-- The expected rank under a uniform distribution over subsets of U. -/
noncomputable def expectedUniformRank (cl : Set U → Set U) : ℝ :=
  let totalRank := ∑ S : Finset U, closureRank cl (S : Set U)
  let numSubsets := (2 : ℝ) ^ Fintype.card U
  totalRank / numSubsets

/-- The randomized expected bound (n/2). -/
theorem randomized_expected_bound [DecidableEq U] (cl : Set U → Set U) (n : ℝ)
    (h_n : n = Fintype.card U)
    (h_symm : ∀ (S : Finset U), closureRank cl S + closureRank cl (Sᶜ : Finset U) = n) :
    expectedUniformRank cl = n / 2 := by
  have h_sum_compl : ∑ S : Finset U, closureRank cl (Sᶜ : Finset U) = ∑ S : Finset U, closureRank cl S := by
    apply Finset.sum_bij (fun (S : Finset U) _ => Sᶜ)
    · intro S _
      exact Finset.mem_univ _
    · intro S₁ _ S₂ _ h
      exact compl_inj_iff.mp h
    · intro S _
      use Sᶜ
      refine ⟨Finset.mem_univ _, compl_compl S⟩
    · intro S _
      rfl
  have h_double_sum : 2 * ∑ S : Finset U, closureRank cl (S : Set U) = ∑ S : Finset U, n := by
    calc
      2 * ∑ S : Finset U, closureRank cl (S : Set U) = (∑ S : Finset U, closureRank cl (S : Set U)) + (∑ S : Finset U, closureRank cl (S : Set U)) := by ring
      _ = (∑ S : Finset U, closureRank cl (S : Set U)) + (∑ S : Finset U, closureRank cl (Sᶜ : Finset U)) := by rw [h_sum_compl]
      _ = ∑ S : Finset U, (closureRank cl (S : Set U) + closureRank cl (Sᶜ : Finset U)) := Finset.sum_add_distrib.symm
      _ = ∑ S : Finset U, n := Finset.sum_congr rfl (fun S _ => h_symm S)
  have h_sum_n : ∑ S : Finset U, n = (Fintype.card (Finset U) : ℝ) * n := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have h_card_finset : (Fintype.card (Finset U) : ℝ) = (2 : ℝ) ^ Fintype.card U := by
    rw [Fintype.card_finset]
    push_cast
    rfl
  have h_total_rank : ∑ S : Finset U, closureRank cl (S : Set U) = ((2 : ℝ) ^ Fintype.card U * n) / 2 := by
    calc
      ∑ S : Finset U, closureRank cl (S : Set U) = (2 * ∑ S : Finset U, closureRank cl (S : Set U)) / 2 := by ring
      _ = (∑ S : Finset U, n) / 2 := by rw [h_double_sum]
      _ = ((Fintype.card (Finset U) : ℝ) * n) / 2 := by rw [h_sum_n]
      _ = ((2 : ℝ) ^ Fintype.card U * n) / 2 := by rw [h_card_finset]
  change (∑ S : Finset U, closureRank cl (S : Set U)) / ((2 : ℝ) ^ Fintype.card U) = n / 2
  rw [h_total_rank]
  have h_two_pow_ne_zero : (2 : ℝ) ^ Fintype.card U ≠ 0 := by positivity
  calc
    (((2 : ℝ) ^ Fintype.card U * n) / 2) / ((2 : ℝ) ^ Fintype.card U) 
      = (((2 : ℝ) ^ Fintype.card U * n) / ((2 : ℝ) ^ Fintype.card U)) / 2 := by ring
    _ = n / 2 := by rw [mul_div_cancel_left₀ n h_two_pow_ne_zero]

end OntologicalFriction
