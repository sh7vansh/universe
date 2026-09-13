/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Authors: Shivansh Singh
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
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

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
set_option linter.overlappingInstances false

open Real
open Classical
open OntologicalMachine

namespace OntologicalFriction

variable {U : Type} [Fintype U] [LinearOrder U] [WellFoundedLT U]

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


lemma one_le_log_plus_one (cl : Set U → Set U) (Δ : ℝ) (h_Δ : Δ = maxMarginalGain cl) :
    1 ≤ Real.log Δ + 1 := by
  have h_nat : ∃ (n : ℕ), Δ = (n : ℝ) := by
    dsimp [maxMarginalGain] at h_Δ
    exact ⟨Finset.univ.sup (fun x => (cl {x}).toFinite.toFinset.card), h_Δ⟩
  rcases h_nat with ⟨n, rfl⟩
  cases n with
  | zero =>
    rw [Nat.cast_zero, Real.log_zero, zero_add]
  | succ n =>
    have hn : 1 ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have h_log := Real.log_nonneg hn
    linarith

lemma bound_of_le (cl : Set U → Set U) (Δ : ℝ) (h_Δ : Δ = maxMarginalGain cl)
    (greedy opt : Set U) (h_le : greedy.toFinite.toFinset.card ≤ opt.toFinite.toFinset.card) :
    (greedy.toFinite.toFinset.card : ℝ) ≤ (Real.log Δ + 1) * (opt.toFinite.toFinset.card : ℝ) := by
  have h_factor := one_le_log_plus_one cl Δ h_Δ
  have h_o_nonneg : 0 ≤ (opt.toFinite.toFinset.card : ℝ) := by positivity
  calc
    (greedy.toFinite.toFinset.card : ℝ) ≤ (opt.toFinite.toFinset.card : ℝ) := by exact_mod_cast h_le
    _ = 1 * (opt.toFinite.toFinset.card : ℝ) := by ring
    _ ≤ (Real.log Δ + 1) * (opt.toFinite.toFinset.card : ℝ) := by nlinarith

lemma opt_empty_of_card_zero (opt : Set U) (h : opt.toFinite.toFinset.card = 0) : opt = ∅ := by
  have h_fin : opt.toFinite.toFinset = ∅ := Finset.card_eq_zero.mp h
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have h_in : x ∈ opt.toFinite.toFinset := by rwa [Set.Finite.mem_toFinset]
  rw [h_fin] at h_in
  simp at h_in

lemma B_seq_empty_of_cl_empty (cl : Set U → Set U) (phi : DiscoveryOperator U)
    (h_cl_empty : cl ∅ = Set.univ) (o : Ordinal.{0}) :
    B_seq cl phi o = ∅ := by
  induction o using Ordinal.limitRecOn with
  | zero => exact B_seq_zero cl phi
  | add_one a ih =>
    rw [B_seq_add_one, ih, h_cl_empty]
    have h_not : ¬ (Set.univ ⊂ (Set.univ : Set U)) := ssubset_irrefl _
    exact dif_neg h_not
  | limit a ha ih =>
    have h_lim : B_seq cl phi a = ⋃ (b : Ordinal.{0}) (hb : b < a), B_seq cl phi b := by
      dsimp [B_seq]
      exact Ordinal.limitRecOn_limit _ _ _ _ ha
    rw [h_lim]
    ext y
    simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
    rintro ⟨b, hb, hby⟩
    have := ih b hb
    rw [this] at hby
    exact hby

lemma sieve_output_empty_of_cl_empty (cl : Set U → Set U) (phi : DiscoveryOperator U)
    (h_cl_empty : cl ∅ = Set.univ) :
    sieve_output cl phi = ∅ := by
  dsimp [sieve_output]
  ext x
  simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
  rintro ⟨o, ho⟩
  have := B_seq_empty_of_cl_empty cl phi h_cl_empty o
  rw [this] at ho
  exact ho

lemma greedy_empty_of_opt_zero (cl : Set U → Set U) (opt greedy : Set U)
    (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : greedy = sieve_output cl (adaptiveGreedyPhi cl))
    (h_opt_zero : opt.toFinite.toFinset.card = 0) :
    greedy.toFinite.toFinset.card = 0 := by
  have h_opt_empty := opt_empty_of_card_zero opt h_opt_zero
  have h_gen := h_opt.1
  dsimp [IsGeneratingSet] at h_gen
  rw [h_opt_empty] at h_gen
  have h_sieve := sieve_output_empty_of_cl_empty cl (adaptiveGreedyPhi cl) h_gen
  rw [h_greedy, h_sieve]
  simp

lemma closureRank_univ_of_gen (cl : Set U → Set U) (S : Set U) (h : cl S = Set.univ) :
    closureRank cl S = Fintype.card U := by
  dsimp [closureRank]
  have h_fin : (cl S).toFinite.toFinset = Finset.univ := by
    ext x
    simp [h]
  rw [h_fin, Finset.card_univ]



lemma closureRank_mono [Fintype U] (cl : Set U → Set U) [ClosureSystem cl] : 
    Monotone (closureRank cl) := by
  intro A B hAB
  dsimp [closureRank]
  have h_cl_subset : cl A ⊆ cl B := ClosureSystem.monotone A B hAB
  have h_fin : (cl A).toFinite.toFinset ⊆ (cl B).toFinite.toFinset := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact h_cl_subset hx
  exact_mod_cast Finset.card_le_card h_fin

lemma cl_union_eq_cl_cl_union [Fintype U] (cl : Set U → Set U) [ClosureSystem cl] (B : Set U) (x : U) :
    cl (B ∪ {x}) = cl (cl B ∪ {x}) := by
  apply Set.Subset.antisymm
  · apply ClosureSystem.monotone
    apply Set.union_subset_union_left
    exact ClosureSystem.extensive B
  · have h1 : cl B ⊆ cl (B ∪ {x}) := ClosureSystem.monotone B (B ∪ {x}) Set.subset_union_left
    have h2 : ({x} : Set U) ⊆ cl (B ∪ {x}) := by
      intro y hy
      apply ClosureSystem.extensive
      exact Set.subset_union_right hy
    have h3 : cl B ∪ {x} ⊆ cl (B ∪ {x}) := Set.union_subset h1 h2
    have h4 : cl (cl B ∪ {x}) ⊆ cl (cl (B ∪ {x})) := ClosureSystem.monotone _ _ h3
    have hid : cl (cl (B ∪ {x})) = cl (B ∪ {x}) := ClosureSystem.idempotent (B ∪ {x})
    rwa [hid] at h4

lemma closureRank_union_eq [Fintype U] (cl : Set U → Set U) [ClosureSystem cl] (B : Set U) (x : U) :
    closureRank cl (B ∪ {x}) = closureRank cl (cl B ∪ {x}) := by
  have h := cl_union_eq_cl_cl_union cl B x
  dsimp [closureRank]
  have h_eq : (cl (B ∪ {x})).toFinite.toFinset = (cl (cl B ∪ {x})).toFinite.toFinset := by
    ext y
    simp only [Set.Finite.mem_toFinset]
    rw [h]
  rw [h_eq]

lemma closureRank_cl_eq (cl : Set U → Set U) [ClosureSystem cl] (S : Set U) :
    closureRank cl (cl S) = closureRank cl S := by
  have hid : cl (cl S) = cl S := ClosureSystem.idempotent S
  dsimp [closureRank]
  have h_eq : (cl (cl S)).toFinite.toFinset = (cl S).toFinite.toFinset := by
    ext y
    simp only [Set.Finite.mem_toFinset]
    rw [hid]
  rw [h_eq]

lemma submodular_finset_le (f : Set U → ℝ) (hf : IsSubmodular f)
    (A : Set U) (s : Finset U) :
    f (A ∪ ↑s) - f A ≤ ∑ x ∈ s, (f (A ∪ {x}) - f A) := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s has ih =>
    rw [Finset.coe_insert, Set.union_insert, Finset.sum_insert has]
    have h_split : f (insert a (A ∪ ↑s)) - f A = (f (insert a (A ∪ ↑s)) - f (A ∪ ↑s)) + (f (A ∪ ↑s) - f A) := by ring
    rw [h_split]
    have h_ins_a : insert a A = A ∪ {a} := by
      ext x
      simp
    by_cases ha_in : a ∈ A ∪ (s : Set U)
    · have h_ins : insert a (A ∪ ↑s) = A ∪ ↑s := Set.insert_eq_of_mem ha_in
      rw [h_ins, sub_self, zero_add]
      cases ha_in with
      | inl haA =>
        have h_Aa : A ∪ {a} = A := by
          ext x
          simp [haA]
        rw [h_Aa, sub_self, zero_add]
        exact ih
      | inr has_mem =>
        rw [Finset.mem_coe] at has_mem
        exact (has has_mem).elim
    · have h_sub : f (insert a (A ∪ ↑s)) - f (A ∪ ↑s) ≤ f (insert a A) - f A := by
        apply hf A (A ∪ ↑s) a (Set.subset_union_left) ha_in
      rw [h_ins_a] at h_sub
      linarith

lemma sum_le_card_mul {α : Type} (s : Finset α) (g : α → ℝ) (M : ℝ)
    (h : ∀ x ∈ s, g x ≤ M) :
    ∑ x ∈ s, g x ≤ (s.card : ℝ) * M := by
  have h1 : ∑ x ∈ s, g x ≤ ∑ x ∈ s, M := Finset.sum_le_sum h
  have h2 : ∑ x ∈ s, M = (s.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

lemma deficit_zero_le (cl : Set U → Set U) (opt : Set U) (h_submod : IsSubmodularClosure cl)
    (h_opt : IsOptimalGenerator cl opt) (Δ : ℝ) (h_Δ : Δ = maxMarginalGain cl) :
    (Fintype.card U : ℝ) - closureRank cl ∅ ≤ (opt.toFinite.toFinset.card : ℝ) * Δ := by
  have h_gen : cl opt = Set.univ := h_opt.1
  have h_rank_opt := closureRank_univ_of_gen cl opt h_gen
  have h_sub_le := submodular_finset_le (closureRank cl) h_submod ∅ opt.toFinite.toFinset
  rw [Set.empty_union, Set.Finite.coe_toFinset, h_rank_opt] at h_sub_le
  have h_each_le : ∀ x ∈ opt.toFinite.toFinset, closureRank cl (∅ ∪ {x}) - closureRank cl ∅ ≤ Δ := by
    intro x hx
    rw [Set.empty_union]
    dsimp [closureRank]
    have h_card_le : ((cl {x}).toFinite.toFinset.card : ℝ) ≤ Δ := by
      rw [h_Δ, maxMarginalGain]
      have h_le := Finset.le_sup (f := fun y => (cl {y}).toFinite.toFinset.card) (Finset.mem_univ x)
      exact_mod_cast h_le
    have h_empty_nonneg : 0 ≤ ((cl ∅).toFinite.toFinset.card : ℝ) := by positivity
    linarith
  have h_sum_le := sum_le_card_mul opt.toFinite.toFinset (fun x => closureRank cl (∅ ∪ {x}) - closureRank cl ∅) Δ h_each_le
  linarith

lemma div_sub_le_log_sub (u v : ℝ) (hv : 0 < v) (hvu : v ≤ u) :
    (u - v) / u ≤ Real.log u - Real.log v := by
  have hu : 0 < u := hv.trans_le hvu
  have hdiv_pos : 0 < v / u := div_pos hv hu
  have h_log_le := Real.log_le_sub_one_of_pos hdiv_pos
  rw [Real.log_div hv.ne' hu.ne'] at h_log_le
  have h_alg : v / u - 1 = - ((u - v) / u) := by
    calc
      v / u - 1 = v / u - u / u := by rw [div_self hu.ne']
      _ = (v - u) / u := by rw [sub_div]
      _ = - ((u - v) / u) := by ring
  rw [h_alg] at h_log_le
  linarith

lemma sum_log_telescope (n : ℕ) (u : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, (Real.log (u i) - Real.log (u (i + 1))) =
    Real.log (u 0) - Real.log (u n) :=
  Finset.sum_range_sub' (fun i => Real.log (u i)) n

theorem analytic_greedy_bound_m (k m : ℕ) (hm : 1 ≤ m) (h_km : m < k) (Δ : ℝ) (hΔ : 0 < Δ)
    (u : ℕ → ℝ)
    (h_step : ∀ i < k - m, 1 / (m : ℝ) ≤ (u i - u (i + 1)) / u i)
    (h_pos : ∀ i < k - m, 0 < u (i + 1))
    (h_le : ∀ i < k - m, u (i + 1) ≤ u i)
    (h_u0 : u 0 ≤ (m : ℝ) * Δ)
    (h_u0_pos : 0 < u 0)
    (h_ukm : (m : ℝ) ≤ u (k - m)) :
    (k : ℝ) ≤ (Real.log Δ + 1) * (m : ℝ) := by
  have hm_pos : 0 < (m : ℝ) := by positivity
  have h_km_pos : 0 < k - m := by omega
  have h_sum_le : ∑ i ∈ Finset.range (k - m), (1 / (m : ℝ)) ≤
      ∑ i ∈ Finset.range (k - m), (Real.log (u i) - Real.log (u (i + 1))) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 := h_step i hi
    have h2 := div_sub_le_log_sub (u i) (u (i + 1)) (h_pos i hi) (h_le i hi)
    exact h1.trans h2
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range] at h_sum_le
  rw [sum_log_telescope (k - m) u] at h_sum_le
  have h_ukm_pos : 0 < u (k - m) := by linarith
  have h_sub_log : Real.log (u 0) - Real.log (u (k - m)) ≤ Real.log Δ := by
    have h_log_u0 : Real.log (u 0) ≤ Real.log ((m : ℝ) * Δ) := Real.log_le_log h_u0_pos h_u0
    have h_log_ukm : Real.log (m : ℝ) ≤ Real.log (u (k - m)) := Real.log_le_log hm_pos h_ukm
    have h_log_prod : Real.log ((m : ℝ) * Δ) = Real.log (m : ℝ) + Real.log Δ := Real.log_mul hm_pos.ne' hΔ.ne'
    rw [h_log_prod] at h_log_u0
    linarith
  have h_card_km : ((k - m : ℕ) : ℝ) = (k : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  rw [h_card_km] at h_sum_le
  have h_div_le : ((k : ℝ) - (m : ℝ)) / (m : ℝ) ≤ Real.log Δ := by
    calc
      ((k : ℝ) - (m : ℝ)) / (m : ℝ) = ((k : ℝ) - (m : ℝ)) * (1 / (m : ℝ)) := by ring
      _ ≤ Real.log (u 0) - Real.log (u (k - m)) := h_sum_le
      _ ≤ Real.log Δ := h_sub_log
  have h_mult : (k : ℝ) - (m : ℝ) ≤ Real.log Δ * (m : ℝ) := (div_le_iff₀ hm_pos).mp h_div_le
  calc
    (k : ℝ) = ((k : ℝ) - (m : ℝ)) + (m : ℝ) := by ring
    _ ≤ Real.log Δ * (m : ℝ) + (m : ℝ) := by linarith
    _ = (Real.log Δ + 1) * (m : ℝ) := by ring

noncomputable def greedyDeficit (cl : Set U → Set U) (i : ℕ) : ℝ :=
  (Fintype.card U : ℝ) - closureRank cl (B_nat cl (adaptiveGreedyPhi cl) i)

lemma greedyDeficit_zero (cl : Set U → Set U) :
    greedyDeficit cl 0 = (Fintype.card U : ℝ) - closureRank cl ∅ := by
  dsimp [greedyDeficit, B_nat]

lemma greedyDeficit_zero_le (cl : Set U → Set U) (opt : Set U) (h_submod : IsSubmodularClosure cl)
    (h_opt : IsOptimalGenerator cl opt) (Δ : ℝ) (h_Δ : Δ = maxMarginalGain cl) :
    greedyDeficit cl 0 ≤ (opt.toFinite.toFinset.card : ℝ) * Δ := by
  rw [greedyDeficit_zero]
  exact deficit_zero_le cl opt h_submod h_opt Δ h_Δ

lemma greedyDeficit_zero_pos (cl : Set U → Set U) (opt : Set U)
    (h_opt : IsOptimalGenerator cl opt) (h_opt_pos : 1 ≤ opt.toFinite.toFinset.card) :
    0 < greedyDeficit cl 0 := by
  rw [greedyDeficit_zero]
  by_contra h_le
  push Not at h_le
  dsimp [closureRank] at h_le
  have h1 : (cl ∅).toFinite.toFinset.card ≤ Fintype.card U := Finset.card_le_univ _
  have h_cast : (Fintype.card U : ℝ) ≤ ((cl ∅).toFinite.toFinset.card : ℝ) := by linarith
  have h_le_nat : Fintype.card U ≤ (cl ∅).toFinite.toFinset.card := by exact_mod_cast h_cast
  have h_card_univ : (cl ∅).toFinite.toFinset.card = Fintype.card U := by omega
  have h_cl_univ : (cl ∅).toFinite.toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ h_card_univ
  have h_gen : IsGeneratingSet cl ∅ := by
    dsimp [IsGeneratingSet]
    ext x
    simp only [Set.mem_univ, iff_true]
    have hx := Finset.mem_univ x
    rw [← h_cl_univ] at hx
    rwa [Set.Finite.mem_toFinset] at hx
  have h_opt_le := h_opt.2 ∅ h_gen
  have h_empty_card : (∅ : Set U).toFinite.toFinset.card = 0 := by simp
  rw [h_empty_card] at h_opt_le
  omega

lemma B_nat_subset_succ (cl : Set U → Set U) (phi : DiscoveryOperator U) (n : ℕ) :
    B_nat cl phi n ⊆ B_nat cl phi (n + 1) := by
  dsimp [B_nat]
  split_ifs with h
  · exact Set.subset_union_left
  · exact Set.Subset.refl _

lemma B_nat_card_le (cl : Set U → Set U) (phi : DiscoveryOperator U) (n : ℕ) :
    (B_nat cl phi n).toFinite.toFinset.card ≤ n := by
  induction n with
  | zero =>
    simp [B_nat]
  | succ n ih =>
    dsimp [B_nat]
    split_ifs with h
    · have h_ins : (B_nat cl phi n ∪ {phi (cl (B_nat cl phi n)) h}).toFinite.toFinset =
          insert (phi (cl (B_nat cl phi n)) h) (B_nat cl phi n).toFinite.toFinset := by
        ext y
        simp
      rw [h_ins]
      have h_card := Finset.card_insert_le (phi (cl (B_nat cl phi n)) h) (B_nat cl phi n).toFinite.toFinset
      omega
    · exact ih.trans (Nat.le_succ n)

lemma B_nat_succ_of_cl_univ (cl : Set U → Set U) (phi : DiscoveryOperator U) (n : ℕ)
    (h : cl (B_nat cl phi n) = Set.univ) :
    B_nat cl phi (n + 1) = B_nat cl phi n := by
  dsimp [B_nat]
  have h_not : ¬ (cl (B_nat cl phi n) ⊂ Set.univ) := by
    rw [h]
    exact ssubset_irrefl _
  rw [dif_neg h_not]

lemma adaptiveGreedy_gain_ge (cl : Set U → Set U) (C : Set U) (hC : C ⊂ Set.univ)
    (x : U) (hx : x ∈ Cᶜ) :
    (cl (C ∪ {x})).toFinite.toFinset.card ≤ (cl (C ∪ {adaptiveGreedyPhi cl C hC})).toFinite.toFinset.card := by
  have h := Classical.choose_spec (show ∃ x ∈ Cᶜ, ∀ y ∈ Cᶜ,
      (cl (C ∪ {y})).toFinite.toFinset.card ≤ (cl (C ∪ {x})).toFinite.toFinset.card from ?_)
  · exact h.2 x hx
  · let compl := Cᶜ
    have h_nonempty : compl.Nonempty := Set.nonempty_compl.mpr hC.ne
    have h_fin : compl.Finite := Set.toFinite compl
    have h_finset_nonempty : h_fin.toFinset.Nonempty := h_fin.toFinset_nonempty.mpr h_nonempty
    rcases Finset.exists_max_image h_fin.toFinset (fun (y : U) => (cl (C ∪ {y})).toFinite.toFinset.card) h_finset_nonempty with ⟨x, hx, hmax⟩
    refine ⟨x, ?_, ?_⟩
    · rwa [Set.Finite.mem_toFinset] at hx
    · intro y hy
      have hy_finset : y ∈ h_fin.toFinset := by rwa [Set.Finite.mem_toFinset]
      exact hmax y hy_finset

lemma each_opt_gain_le (cl : Set U → Set U) (C : Set U) (hC : C ⊂ Set.univ) (x : U)
    (h_nonneg : closureRank cl C ≤ closureRank cl (C ∪ {adaptiveGreedyPhi cl C hC})) :
    closureRank cl (C ∪ {x}) - closureRank cl C ≤
    closureRank cl (C ∪ {adaptiveGreedyPhi cl C hC}) - closureRank cl C := by
  by_cases hx : x ∈ C
  · have h_eq : C ∪ {x} = C := by
      ext y
      simp [hx]
    rw [h_eq, sub_self]
    linarith
  · have hx_compl : x ∈ Cᶜ := hx
    have h_le := adaptiveGreedy_gain_ge cl C hC x hx_compl
    dsimp [closureRank]
    exact sub_le_sub_right (by exact_mod_cast h_le) _

lemma sum_opt_gain_le (cl : Set U → Set U) (C : Set U) (hC : C ⊂ Set.univ) (opt : Set U)
    (h_nonneg : closureRank cl C ≤ closureRank cl (C ∪ {adaptiveGreedyPhi cl C hC})) :
    ∑ x ∈ opt.toFinite.toFinset, (closureRank cl (C ∪ {x}) - closureRank cl C) ≤
    (opt.toFinite.toFinset.card : ℝ) * (closureRank cl (C ∪ {adaptiveGreedyPhi cl C hC}) - closureRank cl C) := by
  have h_each : ∀ x ∈ opt.toFinite.toFinset,
      closureRank cl (C ∪ {x}) - closureRank cl C ≤
      closureRank cl (C ∪ {adaptiveGreedyPhi cl C hC}) - closureRank cl C := by
    intro x _
    exact each_opt_gain_le cl C hC x h_nonneg
  have h_sum := Finset.sum_le_sum h_each
  rw [Finset.sum_const, nsmul_eq_mul] at h_sum
  exact h_sum

lemma submodular_opt_step_le (cl : Set U → Set U) (h_submod : IsSubmodularClosure cl)
    (C : Set U) (hC : C ⊂ Set.univ) (opt : Set U)
    (h_nonneg : closureRank cl C ≤ closureRank cl (C ∪ {adaptiveGreedyPhi cl C hC})) :
    closureRank cl (C ∪ opt) - closureRank cl C ≤
    (opt.toFinite.toFinset.card : ℝ) * (closureRank cl (C ∪ {adaptiveGreedyPhi cl C hC}) - closureRank cl C) := by
  have h_finset_le := submodular_finset_le (closureRank cl) h_submod C opt.toFinite.toFinset
  rw [Set.Finite.coe_toFinset] at h_finset_le
  have h_sum := sum_opt_gain_le cl C hC opt h_nonneg
  linarith



lemma B_nat_monotone (cl : Set U → Set U) (phi : DiscoveryOperator U) {n m : ℕ} (h : n ≤ m) :
    B_nat cl phi n ⊆ B_nat cl phi m := by
  induction m, h using Nat.le_induction with
  | base => exact Set.Subset.refl _
  | succ m hm ih =>
    exact Set.Subset.trans ih (B_nat_subset_succ cl phi m)

lemma B_nat_eventually_stabilizes (cl : Set U → Set U) (phi : DiscoveryOperator U) :
    ∃ n, B_nat cl phi (n + 1) = B_nat cl phi n := by
  by_contra! h
  have h_strict : ∀ n, B_nat cl phi n ⊂ B_nat cl phi (n + 1) := by
    intro n
    have h_sub := B_nat_subset_succ cl phi n
    have h_ne := h n
    exact Set.ssubset_iff_subset_ne.mpr ⟨h_sub, h_ne.symm⟩
  have h_card : ∀ n, n ≤ (B_nat cl phi n).toFinite.toFinset.card := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h_ss := h_strict n
      have h_fin_ss : (B_nat cl phi n).toFinite.toFinset ⊂ (B_nat cl phi (n + 1)).toFinite.toFinset := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro x hx
          rw [Set.Finite.mem_toFinset] at hx ⊢
          exact h_ss.1 hx
        · intro h_eq
          rw [Set.Finite.toFinset_inj] at h_eq
          exact h_ss.ne h_eq
      have h_lt := Finset.card_lt_card h_fin_ss
      omega
  have h_max := h_card (Fintype.card U + 1)
  have h_le_univ : (B_nat cl phi (Fintype.card U + 1)).toFinite.toFinset.card ≤ Fintype.card U :=
    Finset.card_le_univ _
  omega

noncomputable def terminationIndex [Fintype U] (cl : Set U → Set U) (phi : DiscoveryOperator U) : ℕ :=
  Nat.find (B_nat_eventually_stabilizes cl phi)

lemma B_nat_strict_mono [Fintype U] (cl : Set U → Set U) [ClosureSystem cl] 
    (phi : DiscoveryOperator U) (i : ℕ) (h_lt : i < terminationIndex cl phi) :
    B_nat cl phi i ⊂ B_nat cl phi (i + 1) := by
  have h_not := Nat.find_min (B_nat_eventually_stabilizes cl phi) h_lt
  have h_sub := B_nat_subset_succ cl phi i
  exact Set.ssubset_iff_subset_ne.mpr ⟨h_sub, fun h_eq => h_not h_eq.symm⟩

noncomputable def B_step (cl : Set U → Set U) (phi : DiscoveryOperator U) (X : Set U) : Set U :=
  if h : cl X ⊂ Set.univ then X ∪ {phi (cl X) h} else X

lemma B_nat_stabilizes_add (cl : Set U → Set U) (phi : DiscoveryOperator U) (k : ℕ) :
    B_nat cl phi (terminationIndex cl phi + k) = B_nat cl phi (terminationIndex cl phi) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_step : B_nat cl phi (terminationIndex cl phi + k + 1) = B_nat cl phi (terminationIndex cl phi + k) := by
      change B_step cl phi (B_nat cl phi (terminationIndex cl phi + k)) = B_nat cl phi (terminationIndex cl phi + k)
      rw [ih]
      exact Nat.find_spec (B_nat_eventually_stabilizes cl phi)
    have h_eq : terminationIndex cl phi + (k + 1) = terminationIndex cl phi + k + 1 := by omega
    rw [h_eq, h_step, ih]

lemma B_nat_stabilizes [Fintype U] (cl : Set U → Set U) [ClosureSystem cl] 
    (phi : DiscoveryOperator U) (i : ℕ) (h_ge : terminationIndex cl phi ≤ i) :
    B_nat cl phi i = B_nat cl phi (terminationIndex cl phi) := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h_ge
  exact B_nat_stabilizes_add cl phi k

lemma B_seq_eq_B_nat (cl : Set U → Set U) (phi : DiscoveryOperator U) (o : Ordinal.{0}) :
    ∃ n ≤ terminationIndex cl phi, B_seq cl phi o = B_nat cl phi n := by
  induction o using Ordinal.limitRecOn with
  | zero =>
    use 0
    refine ⟨Nat.zero_le _, ?_⟩
    exact B_seq_zero cl phi
  | add_one a ih =>
    rcases ih with ⟨n, hn, hn_eq⟩
    have h_seq_succ : B_seq cl phi (a + 1) = B_step cl phi (B_seq cl phi a) := by
      rw [B_seq_add_one]
      rfl
    rw [h_seq_succ, hn_eq]
    by_cases h_lt : n < terminationIndex cl phi
    · use n + 1
      refine ⟨h_lt, ?_⟩
      rfl
    · have hn_eq_T : n = terminationIndex cl phi := by omega
      use terminationIndex cl phi
      refine ⟨le_rfl, ?_⟩
      subst hn_eq_T
      exact Nat.find_spec (B_nat_eventually_stabilizes cl phi)
  | limit a ha ih =>
    let S : Set ℕ := { n | n ≤ terminationIndex cl phi ∧ ∃ b < a, B_seq cl phi b = B_nat cl phi n }
    have hS_sub : S ⊆ Set.Iic (terminationIndex cl phi) := fun n hn => hn.1
    have hS_fin : S.Finite := (Set.finite_Iic (terminationIndex cl phi)).subset hS_sub
    have hS_nonempty : S.Nonempty := by
      have h0 : 0 < a := ha.pos
      rcases ih 0 h0 with ⟨n, hn, hnb⟩
      exact ⟨n, ⟨hn, ⟨0, h0, hnb⟩⟩⟩
    have h_finset_nonempty : hS_fin.toFinset.Nonempty := hS_fin.toFinset_nonempty.mpr hS_nonempty
    let m := hS_fin.toFinset.max' h_finset_nonempty
    have hm_in : m ∈ hS_fin.toFinset := Finset.max'_mem hS_fin.toFinset h_finset_nonempty
    rw [Set.Finite.mem_toFinset] at hm_in
    rcases hm_in.2 with ⟨b0, hb0, hb0_eq⟩
    use m
    refine ⟨hm_in.1, ?_⟩
    have h_lim : B_seq cl phi a = ⋃ (b : Ordinal.{0}) (hb : b < a), B_seq cl phi b := by
      dsimp [B_seq]
      exact Ordinal.limitRecOn_limit _ _ _ _ ha
    rw [h_lim]
    apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      rcases hx with ⟨b, hb, hxb⟩
      rcases ih b hb with ⟨k, hk, hk_eq⟩
      rw [hk_eq] at hxb
      have hk_in : k ∈ S := ⟨hk, ⟨b, hb, hk_eq⟩⟩
      have hk_finset : k ∈ hS_fin.toFinset := by rwa [Set.Finite.mem_toFinset]
      have h_le_m : k ≤ m := Finset.le_max' hS_fin.toFinset k hk_finset
      exact B_nat_monotone cl phi h_le_m hxb
    · intro x hx
      simp only [Set.mem_iUnion]
      exact ⟨b0, hb0, by rwa [hb0_eq]⟩

lemma sieve_output_eq_B_nat_termination [Fintype U] (cl : Set U → Set U) [ClosureSystem cl]
    (phi : DiscoveryOperator U) :
    sieve_output cl phi = B_nat cl phi (terminationIndex cl phi) := by
  apply Set.Subset.antisymm
  · intro x hx
    dsimp [sieve_output] at hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨o, ho⟩
    rcases B_seq_eq_B_nat cl phi o with ⟨n, hn, hn_eq⟩
    rw [hn_eq] at ho
    exact B_nat_monotone cl phi hn ho
  · exact B_nat_subset_sieve_output cl phi (terminationIndex cl phi)

lemma B_nat_card_eq_of_lt (cl : Set U → Set U) [ClosureSystem cl] (phi : DiscoveryOperator U) (n : ℕ)
    (hn : n ≤ terminationIndex cl phi) :
    (B_nat cl phi n).toFinite.toFinset.card = n := by
  induction n with
  | zero => simp [B_nat]
  | succ n ih =>
    have hn_lt : n < terminationIndex cl phi := by omega
    have ih_val := ih (by omega)
    have h_ss := B_nat_strict_mono cl phi n hn_lt
    dsimp [B_nat]
    split_ifs with h_cl
    · have h_ins : (B_nat cl phi n ∪ {phi (cl (B_nat cl phi n)) h_cl}).toFinite.toFinset =
          insert (phi (cl (B_nat cl phi n)) h_cl) (B_nat cl phi n).toFinite.toFinset := by
        ext y
        simp
      rw [h_ins]
      have hm_not : phi (cl (B_nat cl phi n)) h_cl ∉ (B_nat cl phi n).toFinite.toFinset := by
        rw [Set.Finite.mem_toFinset]
        intro hm_in
        apply h_ss.ne
        apply Set.Subset.antisymm
        · exact B_nat_subset_succ cl phi n
        · intro y hy
          dsimp [B_nat] at hy
          rw [dif_pos h_cl] at hy
          cases hy with
          | inl hy_B => exact hy_B
          | inr hy_m =>
            rw [Set.mem_singleton_iff] at hy_m
            rwa [hy_m]
      rw [Finset.card_insert_of_notMem hm_not, ih_val]
    · apply (h_ss.ne _).elim
      dsimp [B_nat]
      rw [dif_neg h_cl]

lemma greedy_card_eq_terminationIndex [Fintype U] (cl : Set U → Set U) [ClosureSystem cl] :
    (sieve_output cl (adaptiveGreedyPhi cl)).toFinite.toFinset.card = terminationIndex cl (adaptiveGreedyPhi cl) := by
  rw [sieve_output_eq_B_nat_termination cl (adaptiveGreedyPhi cl)]
  exact B_nat_card_eq_of_lt cl (adaptiveGreedyPhi cl) (terminationIndex cl (adaptiveGreedyPhi cl)) le_rfl

lemma closureRank_step_ge_one (cl : Set U → Set U) [ClosureSystem cl] (n : ℕ)
    (hn : n < terminationIndex cl (adaptiveGreedyPhi cl)) :
    1 ≤ closureRank cl (B_nat cl (adaptiveGreedyPhi cl) (n + 1)) - closureRank cl (B_nat cl (adaptiveGreedyPhi cl) n) := by
  have h_ss := B_nat_strict_mono cl (adaptiveGreedyPhi cl) n hn
  have h_sub := B_nat_subset_succ cl (adaptiveGreedyPhi cl) n
  dsimp [B_nat] at h_ss
  split_ifs at h_ss with h_cl
  · let x := adaptiveGreedyPhi cl (cl (B_nat cl (adaptiveGreedyPhi cl) n)) h_cl
    have h_spec := Classical.choose_spec (show ∃ x ∈ (cl (B_nat cl (adaptiveGreedyPhi cl) n))ᶜ, ∀ y ∈ (cl (B_nat cl (adaptiveGreedyPhi cl) n))ᶜ,
        (cl ((cl (B_nat cl (adaptiveGreedyPhi cl) n)) ∪ {y})).toFinite.toFinset.card ≤ (cl ((cl (B_nat cl (adaptiveGreedyPhi cl) n)) ∪ {x})).toFinite.toFinset.card from ?_)
    · have hx_not : x ∉ cl (B_nat cl (adaptiveGreedyPhi cl) n) := h_spec.1
      have hx_in_succ : x ∈ cl (B_nat cl (adaptiveGreedyPhi cl) (n + 1)) := by
        dsimp [B_nat]
        rw [dif_pos h_cl]
        apply ClosureSystem.extensive
        exact Set.subset_union_right (Set.mem_singleton x)
      have h_cl_sub : cl (B_nat cl (adaptiveGreedyPhi cl) n) ⊆ cl (B_nat cl (adaptiveGreedyPhi cl) (n + 1)) :=
        ClosureSystem.monotone _ _ (B_nat_subset_succ cl (adaptiveGreedyPhi cl) n)
      have h_cl_ss : cl (B_nat cl (adaptiveGreedyPhi cl) n) ⊂ cl (B_nat cl (adaptiveGreedyPhi cl) (n + 1)) := by
        rw [Set.ssubset_iff_subset_ne]
        refine ⟨h_cl_sub, ?_⟩
        intro heq
        rw [heq] at hx_not
        exact hx_not hx_in_succ
      have h_fin_ss : (cl (B_nat cl (adaptiveGreedyPhi cl) n)).toFinite.toFinset ⊂
          (cl (B_nat cl (adaptiveGreedyPhi cl) (n + 1))).toFinite.toFinset := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro y hy
          rw [Set.Finite.mem_toFinset] at hy ⊢
          exact h_cl_ss.1 hy
        · intro h_eq
          rw [Set.Finite.toFinset_inj] at h_eq
          exact h_cl_ss.ne h_eq
      have h_lt := Finset.card_lt_card h_fin_ss
      dsimp [closureRank]
      have : ((cl (B_nat cl (adaptiveGreedyPhi cl) n)).toFinite.toFinset.card : ℝ) + 1 ≤
          ((cl (B_nat cl (adaptiveGreedyPhi cl) (n + 1))).toFinite.toFinset.card : ℝ) := by
        exact_mod_cast h_lt
      linarith
    · let compl := (cl (B_nat cl (adaptiveGreedyPhi cl) n))ᶜ
      have h_nonempty : compl.Nonempty := Set.nonempty_compl.mpr h_cl.ne
      have h_fin : compl.Finite := Set.toFinite compl
      rcases Finset.exists_max_image h_fin.toFinset (fun y => (cl ((cl (B_nat cl (adaptiveGreedyPhi cl) n)) ∪ {y})).toFinite.toFinset.card) (h_fin.toFinset_nonempty.mpr h_nonempty) with ⟨x, hx, hmax⟩
      refine ⟨x, ?_, ?_⟩
      · rwa [Set.Finite.mem_toFinset] at hx
      · intro y hy
        exact hmax y (by rwa [Set.Finite.mem_toFinset])
  · exact (h_ss.ne rfl).elim

lemma closureRank_diff_ge (cl : Set U → Set U) [ClosureSystem cl] (j d : ℕ)
    (h : j + d ≤ terminationIndex cl (adaptiveGreedyPhi cl)) :
    (d : ℝ) ≤ closureRank cl (B_nat cl (adaptiveGreedyPhi cl) (j + d)) - closureRank cl (B_nat cl (adaptiveGreedyPhi cl) j) := by
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hd_le : j + d ≤ terminationIndex cl (adaptiveGreedyPhi cl) := by omega
    have ih_val := ih hd_le
    have h_step := closureRank_step_ge_one cl (j + d) (by omega)
    have h_split : closureRank cl (B_nat cl (adaptiveGreedyPhi cl) (j + (d + 1))) - closureRank cl (B_nat cl (adaptiveGreedyPhi cl) j) =
        (closureRank cl (B_nat cl (adaptiveGreedyPhi cl) (j + d + 1)) - closureRank cl (B_nat cl (adaptiveGreedyPhi cl) (j + d))) +
        (closureRank cl (B_nat cl (adaptiveGreedyPhi cl) (j + d)) - closureRank cl (B_nat cl (adaptiveGreedyPhi cl) j)) := by
      have : j + (d + 1) = j + d + 1 := by omega
      rw [this]
      ring
    rw [h_split]
    push_cast
    linarith

lemma div_le_div_of_mul_le {A B M : ℝ} (hA : 0 < A) (hM : 0 < M) (h : A ≤ M * B) :
    1 / M ≤ B / A := by
  rw [div_le_div_iff₀ hM hA]
  calc
    1 * A = A := by ring
    _ ≤ M * B := h
    _ = B * M := by ring

lemma greedyDeficit_mono [LinearOrder U] [WellFoundedLT U] [Fintype U]
    (cl : Set U → Set U) [ClosureSystem cl] (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl) (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl))
    (i : ℕ) (hi : i < greedy.toFinite.toFinset.card - opt.toFinite.toFinset.card) :
    greedyDeficit cl (i + 1) ≤ greedyDeficit cl i := by
  dsimp [greedyDeficit]
  have h_sub := B_nat_subset_succ cl (adaptiveGreedyPhi cl) i
  have h_rank := closureRank_mono cl h_sub
  linarith

lemma greedyDeficit_pos [LinearOrder U] [WellFoundedLT U] [Fintype U]
    (cl : Set U → Set U) [ClosureSystem cl] (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl) (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl))
    (i : ℕ) (hi : i < greedy.toFinite.toFinset.card - opt.toFinite.toFinset.card) :
    0 < greedyDeficit cl (i + 1) := by
  dsimp [greedyDeficit]
  have h_T : greedy.toFinite.toFinset.card = terminationIndex cl (adaptiveGreedyPhi cl) := by
    rw [h_is_greedy_output]
    exact greedy_card_eq_terminationIndex cl
  have hi_T : i + 1 < terminationIndex cl (adaptiveGreedyPhi cl) := by
    by_cases h_opt_zero : opt.toFinite.toFinset.card = 0
    · have h_gz := greedy_empty_of_opt_zero cl opt greedy h_opt h_is_greedy_output h_opt_zero
      rw [h_gz, h_opt_zero] at hi
      omega
    · have h_le := h_opt.2 greedy h_greedy
      rw [h_T] at hi
      omega
  have h_ss := B_nat_strict_mono cl (adaptiveGreedyPhi cl) (i + 1) hi_T
  have h_not_univ : cl (B_nat cl (adaptiveGreedyPhi cl) (i + 1)) ⊂ Set.univ := by
    by_contra! h_not
    have h_eq : cl (B_nat cl (adaptiveGreedyPhi cl) (i + 1)) = Set.univ := by
      apply Set.Subset.antisymm (Set.subset_univ _)
      intro x _
      by_contra hx
      apply h_not
      rw [Set.ssubset_iff_subset_ne]
      refine ⟨Set.subset_univ _, ?_⟩
      intro h_all
      have hx_in : x ∈ cl (B_nat cl (adaptiveGreedyPhi cl) (i + 1)) := by
        rw [h_all]
        trivial
      exact hx hx_in
    have h_step := B_nat_succ_of_cl_univ cl (adaptiveGreedyPhi cl) (i + 1) h_eq
    exact h_ss.ne h_step.symm
  dsimp [closureRank]
  have h_card_lt : (cl (B_nat cl (adaptiveGreedyPhi cl) (i + 1))).toFinite.toFinset.card < Fintype.card U := by
    obtain ⟨x, hx⟩ := Set.nonempty_compl.mpr h_not_univ.ne
    have h_fin_ne : (cl (B_nat cl (adaptiveGreedyPhi cl) (i + 1))).toFinite.toFinset ≠ Finset.univ := by
      intro h_univ
      have hx_in : x ∈ (cl (B_nat cl (adaptiveGreedyPhi cl) (i + 1))).toFinite.toFinset := by
        rw [h_univ]
        exact Finset.mem_univ x
      rw [Set.Finite.mem_toFinset] at hx_in
      exact hx hx_in
    have h_ss_fin : (cl (B_nat cl (adaptiveGreedyPhi cl) (i + 1))).toFinite.toFinset ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, h_fin_ne⟩
    have := Finset.card_lt_card h_ss_fin
    rwa [Finset.card_univ] at this
  exact sub_pos.mpr (by exact_mod_cast h_card_lt)

lemma greedyDeficit_ukm [LinearOrder U] [WellFoundedLT U] [Fintype U]
    (cl : Set U → Set U) [ClosureSystem cl] (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl) (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl)) :
    (opt.toFinite.toFinset.card : ℝ) ≤ greedyDeficit cl (greedy.toFinite.toFinset.card - opt.toFinite.toFinset.card) := by
  let k := greedy.toFinite.toFinset.card
  let m := opt.toFinite.toFinset.card
  have h_le : m ≤ k := h_opt.2 greedy h_greedy
  have h_T : k = terminationIndex cl (adaptiveGreedyPhi cl) := by
    dsimp [k]
    rw [h_is_greedy_output]
    exact greedy_card_eq_terminationIndex cl
  have h_B_k : B_nat cl (adaptiveGreedyPhi cl) k = greedy := by
    have : k = terminationIndex cl (adaptiveGreedyPhi cl) := h_T
    rw [this, h_is_greedy_output, sieve_output_eq_B_nat_termination cl (adaptiveGreedyPhi cl)]
  have h_cl_k : cl (B_nat cl (adaptiveGreedyPhi cl) k) = Set.univ := by
    rw [h_B_k]
    exact h_greedy
  have h_rank_k : closureRank cl (B_nat cl (adaptiveGreedyPhi cl) k) = Fintype.card U :=
    closureRank_univ_of_gen cl (B_nat cl (adaptiveGreedyPhi cl) k) h_cl_k
  have h_diff := closureRank_diff_ge cl (k - m) m (by rw [Nat.sub_add_cancel h_le, h_T])
  rw [Nat.sub_add_cancel h_le] at h_diff
  dsimp [greedyDeficit]
  rw [← h_rank_k]
  exact h_diff

lemma greedyDeficit_step_le [LinearOrder U] [WellFoundedLT U] [Fintype U]
    (cl : Set U → Set U) [ClosureSystem cl] (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl) (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl))
    (i : ℕ) (hi : i < greedy.toFinite.toFinset.card - opt.toFinite.toFinset.card) :
    1 / (opt.toFinite.toFinset.card : ℝ) ≤ (greedyDeficit cl i - greedyDeficit cl (i + 1)) / greedyDeficit cl i := by
  have h_T : greedy.toFinite.toFinset.card = terminationIndex cl (adaptiveGreedyPhi cl) := by
    rw [h_is_greedy_output]
    exact greedy_card_eq_terminationIndex cl
  have h_opt_pos : 0 < opt.toFinite.toFinset.card := by
    by_contra! h0
    have h_opt_zero : opt.toFinite.toFinset.card = 0 := by omega
    have h_gz := greedy_empty_of_opt_zero cl opt greedy h_opt h_is_greedy_output h_opt_zero
    rw [h_gz, h_opt_zero] at hi
    omega
  have hi_T : i < terminationIndex cl (adaptiveGreedyPhi cl) := by
    have h_le := h_opt.2 greedy h_greedy
    rw [h_T] at hi
    omega
  have h_ss_B := B_nat_strict_mono cl (adaptiveGreedyPhi cl) i hi_T
  have hC : cl (B_nat cl (adaptiveGreedyPhi cl) i) ⊂ Set.univ := by
    by_contra! h_not
    have h_eq : cl (B_nat cl (adaptiveGreedyPhi cl) i) = Set.univ := by
      apply Set.Subset.antisymm (Set.subset_univ _)
      intro x _
      by_contra hx
      apply h_not
      rw [Set.ssubset_iff_subset_ne]
      refine ⟨Set.subset_univ _, ?_⟩
      intro h_all
      have hx_in : x ∈ cl (B_nat cl (adaptiveGreedyPhi cl) i) := by
        rw [h_all]
        trivial
      exact hx hx_in
    have h_step := B_nat_succ_of_cl_univ cl (adaptiveGreedyPhi cl) i h_eq
    exact h_ss_B.ne h_step.symm
  let C := cl (B_nat cl (adaptiveGreedyPhi cl) i)
  let x := adaptiveGreedyPhi cl C hC
  have h_Bi_succ : B_nat cl (adaptiveGreedyPhi cl) (i + 1) = B_nat cl (adaptiveGreedyPhi cl) i ∪ {x} := by
    dsimp [B_nat]
    rw [dif_pos hC]
  have h_nonneg : closureRank cl C ≤ closureRank cl (C ∪ {x}) :=
    closureRank_mono cl Set.subset_union_left
  have h_step_le := submodular_opt_step_le cl h_submod C hC opt h_nonneg
  have h_C_opt_gen : cl (C ∪ opt) = Set.univ := by
    have h1 : opt ⊆ C ∪ opt := Set.subset_union_right
    have h2 : cl opt ⊆ cl (C ∪ opt) := ClosureSystem.monotone _ _ h1
    have h3 : cl opt = Set.univ := h_opt.1
    rw [h3] at h2
    exact Set.eq_univ_of_univ_subset h2
  have h_rank_C_opt : closureRank cl (C ∪ opt) = Fintype.card U :=
    closureRank_univ_of_gen cl (C ∪ opt) h_C_opt_gen
  have h_rank_C : closureRank cl C = closureRank cl (B_nat cl (adaptiveGreedyPhi cl) i) :=
    closureRank_cl_eq cl (B_nat cl (adaptiveGreedyPhi cl) i)
  have h_rank_Cx : closureRank cl (C ∪ {x}) = closureRank cl (B_nat cl (adaptiveGreedyPhi cl) (i + 1)) := by
    rw [h_Bi_succ]
    exact (closureRank_union_eq cl (B_nat cl (adaptiveGreedyPhi cl) i) x).symm
  have h_def_i : greedyDeficit cl i = closureRank cl (C ∪ opt) - closureRank cl C := by
    dsimp [greedyDeficit]
    rw [h_rank_C_opt, h_rank_C]
  have h_gain : greedyDeficit cl i - greedyDeficit cl (i + 1) = closureRank cl (C ∪ {x}) - closureRank cl C := by
    dsimp [greedyDeficit]
    rw [h_rank_Cx, h_rank_C]
    ring
  rw [← h_def_i, ← h_gain] at h_step_le
  have h_def_pos : 0 < greedyDeficit cl i := by
    have h_mono := greedyDeficit_mono cl opt greedy h_submod h_opt h_greedy h_is_greedy_output i hi
    have h_pos := greedyDeficit_pos cl opt greedy h_submod h_opt h_greedy h_is_greedy_output i hi
    linarith
  have h_opt_real_pos : 0 < (opt.toFinite.toFinset.card : ℝ) := by exact_mod_cast h_opt_pos
  exact div_le_div_of_mul_le h_def_pos h_opt_real_pos h_step_le

theorem greedy_submodular_bound [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) [ClosureSystem cl] (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl)
    (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl))
    (Δ : ℝ) (h_Δ : Δ = maxMarginalGain cl) :
    (greedy.toFinite.toFinset.card : ℝ) ≤ (Real.log Δ + 1) * (opt.toFinite.toFinset.card : ℝ) := by
  by_cases h_opt_zero : opt.toFinite.toFinset.card = 0
  · have h_g_zero := greedy_empty_of_opt_zero cl opt greedy h_opt h_is_greedy_output h_opt_zero
    rw [h_g_zero, h_opt_zero]
    simp
  · have h_opt_pos : 1 ≤ opt.toFinite.toFinset.card := by omega
    by_cases h_le : greedy.toFinite.toFinset.card ≤ opt.toFinite.toFinset.card
    · exact bound_of_le cl Δ h_Δ greedy opt h_le
    · have h_gt : opt.toFinite.toFinset.card < greedy.toFinite.toFinset.card := by omega
      have h_def_pos := greedyDeficit_zero_pos cl opt h_opt h_opt_pos
      have h_def_le := greedyDeficit_zero_le cl opt h_submod h_opt Δ h_Δ
      have h_Δ_pos : 0 < Δ := by
        have : 0 < (opt.toFinite.toFinset.card : ℝ) := by positivity
        nlinarith
      have h_bound := analytic_greedy_bound_m greedy.toFinite.toFinset.card opt.toFinite.toFinset.card
        (by exact_mod_cast h_opt_pos) (by exact_mod_cast h_gt) Δ h_Δ_pos (greedyDeficit cl)
        (by
          intro i hi
          exact greedyDeficit_step_le cl opt greedy h_submod h_opt h_greedy h_is_greedy_output i hi
        )
        (by
          intro i hi
          exact greedyDeficit_pos cl opt greedy h_submod h_opt h_greedy h_is_greedy_output i hi
        )
        (by
          intro i hi
          exact greedyDeficit_mono cl opt greedy h_submod h_opt h_greedy h_is_greedy_output i hi
        )
        (by
          exact h_def_le
        )
        (by
          exact h_def_pos
        )
        (by
          exact greedyDeficit_ukm cl opt greedy h_submod h_opt h_greedy h_is_greedy_output
        )
      exact h_bound

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

theorem advCl_greedy_size_worst_case [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (greedy : Set U) (e_star : U) 
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
