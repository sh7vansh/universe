import MathProject.SubmodularFriction
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

open OntologicalFriction
open OntologicalMachine
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable [Fintype U] [LinearOrder U] [WellFoundedLT U]

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


/-- The core submodular step bound (Pigeonhole principle).
    The optimal solution covers the remaining deficit using |opt| elements.
    By submodularity, the best single element (chosen by greedy) must cover 
    at least 1/|opt| of the remaining gap. -/
lemma greedyDeficit_step_le [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl) (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl))
    (i : ℕ) (hi : i < greedy.toFinite.toFinset.card - opt.toFinite.toFinset.card) :
    1 / (opt.toFinite.toFinset.card : ℝ) ≤ (greedyDeficit cl i - greedyDeficit cl (i + 1)) / greedyDeficit cl i := by
  sorry

/-- Positivity of deficit before termination.
    If the algorithm hasn't terminated, the closure rank is strictly less 
    than the maximum universe rank, meaning the deficit > 0. -/
lemma greedyDeficit_pos [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl) (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl))
    (i : ℕ) (hi : i < greedy.toFinite.toFinset.card - opt.toFinite.toFinset.card) :
    0 < greedyDeficit cl (i + 1) := by
  sorry

/-- Monotonicity of deficit.
    Adding elements strictly increases closure rank, thereby decreasing the 
    deficit to the maximum rank. Thus deficit is non-increasing. -/
lemma greedyDeficit_mono [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl) (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl))
    (i : ℕ) (hi : i < greedy.toFinite.toFinset.card - opt.toFinite.toFinset.card) :
    greedyDeficit cl (i + 1) ≤ greedyDeficit cl i := by
  sorry

/-- Lower bound near termination.
    Every step increases rank by at least 1. If |opt| steps remain to reach 
    maximum rank, the deficit must currently be at least |opt|. -/
lemma greedyDeficit_ukm [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (opt greedy : Set U)
    (h_submod : IsSubmodularClosure cl) (h_opt : IsOptimalGenerator cl opt)
    (h_greedy : IsGeneratingSet cl greedy)
    (h_is_greedy_output : greedy = OntologicalMachine.sieve_output cl (OntologicalMachine.adaptiveGreedyPhi cl)) :
    (opt.toFinite.toFinset.card : ℝ) ≤ greedyDeficit cl (greedy.toFinite.toFinset.card - opt.toFinite.toFinset.card) := by
  sorry

theorem greedy_submodular_bound_ax [LinearOrder U] [WellFoundedLT U] (cl : Set U → Set U) (opt greedy : Set U)
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
