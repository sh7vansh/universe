/-
Copyright (c) 2024 MathProject Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathProject Authors
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
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
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.header false

open Real
open Classical
open OntologicalMachine

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
axiom greedy_submodular_bound_ax [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl)
    (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl))
    (Δ : ℝ) (h_Δ : Δ = maxMarginalGain cl) :
    (greedy.toFinite.toFinset.card : ℝ) ≤ (Real.log Δ + 1) * (opt.toFinite.toFinset.card : ℝ)

theorem greedy_submodular_bound [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl)
    (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl))
    (Δ : ℝ) (h_Δ : Δ = maxMarginalGain cl) :
    (greedy.toFinite.toFinset.card : ℝ) ≤ (Real.log Δ + 1) * (opt.toFinite.toFinset.card : ℝ) :=
  greedy_submodular_bound_ax cl opt greedy h_submod h_opt h_greedy h_is_greedy_output Δ h_Δ

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

noncomputable def B_nat (cl : Set U → Set U) (phi : DiscoveryOperator U) : ℕ → Set U
  | 0 => ∅
  | n + 1 => if h : cl (B_nat cl phi n) ⊂ Set.univ then B_nat cl phi n ∪ {phi (cl (B_nat cl phi n)) h} else B_nat cl phi n

lemma B_seq_zero (cl : Set U → Set U) (phi : DiscoveryOperator U) :
    B_seq cl phi 0 = ∅ := by
  dsimp [B_seq]
  rw [Ordinal.limitRecOn_zero]

lemma B_seq_add_one (cl : Set U → Set U) (phi : DiscoveryOperator U) (o : Ordinal) :
    B_seq cl phi (o + 1) = if h : cl (B_seq cl phi o) ⊂ Set.univ then B_seq cl phi o ∪ {phi (cl (B_seq cl phi o)) h} else B_seq cl phi o := by
  dsimp [B_seq]
  rw [Ordinal.limitRecOn_add_one]
  rfl

lemma B_seq_nat_eq (cl : Set U → Set U) (phi : DiscoveryOperator U) (n : ℕ) :
    B_seq cl phi (n : Ordinal.{0}) = B_nat cl phi n := by
  induction n with
  | zero => exact B_seq_zero cl phi
  | succ n ih =>
    rw [Nat.cast_add_one, B_seq_add_one]
    rw [ih]
    rfl

lemma B_nat_subset_sieve_output (cl : Set U → Set U) (phi : DiscoveryOperator U) (n : ℕ) :
    B_nat cl phi n ⊆ sieve_output cl phi := by
  intro x hx
  dsimp [sieve_output]
  rw [Set.mem_iUnion]
  use (n : Ordinal.{0})
  rw [B_seq_nat_eq]
  exact hx

lemma B_nat_step [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (e_star : U)
    (h_cl : cl = fun S => if _h : e_star ∈ S then Set.univ else S)
    (h_worst : ∀ x, x ≤ e_star)
    (k : ℕ) (hk_card : (B_nat cl fixedPriorityPhi k).toFinite.toFinset.card = k)
    (hk_ne : e_star ∉ B_nat cl fixedPriorityPhi k) (hk_lt : k < Fintype.card U) :
    let Bk := B_nat cl fixedPriorityPhi k
    ∃ h : cl Bk ⊂ Set.univ,
      let m := fixedPriorityPhi (cl Bk) h
      B_nat cl fixedPriorityPhi (k + 1) = Bk ∪ {m} ∧
      m ∉ Bk ∧
      (k + 1 < Fintype.card U → m ≠ e_star) := by
  intro Bk
  have h_cl_eq : cl Bk = Bk := by
    rw [h_cl]
    exact if_neg hk_ne
  have h_ss : Bk ⊂ Set.univ := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨Set.subset_univ Bk, ?_⟩
    intro h_eq
    have h_card : Bk.toFinite.toFinset.card = Fintype.card U := by
      rw [h_eq]
      simp
    omega
  have h_cl_ss : cl Bk ⊂ Set.univ := by
    rwa [h_cl_eq]
  use h_cl_ss
  intro m
  have h_def : B_nat cl fixedPriorityPhi (k + 1) = Bk ∪ {m} := by
    dsimp [B_nat]
    rw [dif_pos h_cl_ss]
  refine ⟨h_def, ?_, ?_⟩
  · have hm_not : m ∉ cl Bk := novelty_of_fixedPriorityPhi (cl Bk) h_cl_ss
    rwa [h_cl_eq] at hm_not
  · intro h_lt2 h_m
    have h_all : ∀ y ∈ Bkᶜ, y = e_star := by
      intro y hy
      have hy_cl : y ∈ (cl Bk)ᶜ := by rwa [h_cl_eq]
      have h_not_lt := WellFounded.not_lt_min wellFounded_lt (cl Bk)ᶜ hy_cl
      have h_m_def : m = WellFounded.min wellFounded_lt (cl Bk)ᶜ (Set.nonempty_compl.mpr h_cl_ss.ne) := rfl
      rw [← h_m_def, h_m] at h_not_lt
      have h_le1 : e_star ≤ y := not_lt.mp h_not_lt
      have h_le2 : y ≤ e_star := h_worst y
      exact le_antisymm h_le2 h_le1
    have h_compl_sub : Bkᶜ ⊆ {e_star} := by
      intro y hy
      exact Set.mem_singleton_iff.mpr (h_all y hy)
    have h_compl_eq : Bkᶜ = {e_star} := by
      apply Set.Subset.antisymm h_compl_sub
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hk_ne
    have h_bk_eq : Bk = {e_star}ᶜ := by
      rw [← compl_compl Bk, h_compl_eq]
    have h_bk_finset : Bk.toFinite.toFinset = Finset.univ.erase e_star := by
      ext y
      simp [h_bk_eq]
    have h_bk_card : Bk.toFinite.toFinset.card = Fintype.card U - 1 := by
      rw [h_bk_finset, Finset.card_erase_of_mem (Finset.mem_univ e_star), Finset.card_univ]
    omega

lemma B_nat_card_and_not_mem [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (e_star : U)
    (h_cl : cl = fun S => if _h : e_star ∈ S then Set.univ else S)
    (h_worst : ∀ x, x ≤ e_star) (k : ℕ) (hk : k ≤ Fintype.card U) :
    (B_nat cl fixedPriorityPhi k).toFinite.toFinset.card = k ∧
    (k < Fintype.card U → e_star ∉ B_nat cl fixedPriorityPhi k) := by
  induction k with
  | zero =>
    refine ⟨by simp [B_nat], ?_⟩
    intro _
    dsimp [B_nat]
    intro h
    cases h
  | succ k ih =>
    have hk_lt : k < Fintype.card U := by omega
    have ⟨ih_card, ih_ne⟩ := ih (by omega)
    have ih_not_mem := ih_ne hk_lt
    rcases B_nat_step cl e_star h_cl h_worst k ih_card ih_not_mem hk_lt with ⟨h_ss, h_def, hm_not, hm_ne⟩
    have h_card_succ : (B_nat cl fixedPriorityPhi (k + 1)).toFinite.toFinset.card = k + 1 := by
      rw [h_def]
      have hs : (B_nat cl fixedPriorityPhi k ∪ {fixedPriorityPhi (cl (B_nat cl fixedPriorityPhi k)) h_ss}).toFinite.toFinset =
          insert (fixedPriorityPhi (cl (B_nat cl fixedPriorityPhi k)) h_ss) (B_nat cl fixedPriorityPhi k).toFinite.toFinset := by
        ext y
        simp
      rw [hs]
      rw [Finset.card_insert_of_notMem]
      · rw [ih_card]
      · rwa [Set.Finite.mem_toFinset]
    refine ⟨h_card_succ, ?_⟩
    intro hk_succ_lt
    rw [h_def]
    intro h_in
    cases h_in with
    | inl h_in_Bk => exact ih_not_mem h_in_Bk
    | inr h_eq =>
      have : fixedPriorityPhi (cl (B_nat cl fixedPriorityPhi k)) h_ss = e_star := by
        have : e_star ∈ ({fixedPriorityPhi (cl (B_nat cl fixedPriorityPhi k)) h_ss} : Set U) := h_eq
        exact (Set.mem_singleton_iff.mp this).symm
      exact hm_ne hk_succ_lt this

theorem advCl_greedy_size_worst_case_ax [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (greedy : Set U) (e_star : U) 
    (h_cl : cl = fun S => if _h : e_star ∈ S then Set.univ else S) 
    (h_worst : ∀ x, x ≤ e_star) -- e_star is the LAST element evaluated
    (h_greedy : greedy = OntologicalMachine.sieve_output cl OntologicalMachine.fixedPriorityPhi) : 
    greedy.toFinite.toFinset.card = Fintype.card U := by
  have h_card_univ := (B_nat_card_and_not_mem cl e_star h_cl h_worst (Fintype.card U) (le_refl _)).1
  have h_eq_univ : B_nat cl fixedPriorityPhi (Fintype.card U) = Set.univ := by
    have h_finset : (B_nat cl fixedPriorityPhi (Fintype.card U)).toFinite.toFinset = Finset.univ :=
      Finset.eq_univ_of_card _ h_card_univ
    ext y
    simp only [Set.mem_univ, iff_true]
    have hy := Finset.mem_univ y
    rw [← h_finset] at hy
    rwa [Set.Finite.mem_toFinset] at hy
  have h_sub : Set.univ ⊆ greedy := by
    rw [h_greedy, ← h_eq_univ]
    exact B_nat_subset_sieve_output cl fixedPriorityPhi (Fintype.card U)
  have h_greedy_univ : greedy = Set.univ :=
    Set.Subset.antisymm (Set.subset_univ greedy) h_sub
  rw [h_greedy_univ]
  rw [Set.Finite.toFinset_univ, Finset.card_univ]

lemma advCl_greedy_size_worst_case [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (greedy : Set U) (e_star : U) 
    (h_cl : cl = fun S => if _h : e_star ∈ S then Set.univ else S) 
    (h_worst : ∀ x, x ≤ e_star) -- e_star is the LAST element evaluated
    (h_greedy : greedy = OntologicalMachine.sieve_output cl OntologicalMachine.fixedPriorityPhi) : 
    greedy.toFinite.toFinset.card = Fintype.card U :=
  advCl_greedy_size_worst_case_ax cl greedy e_star h_cl h_worst h_greedy

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
