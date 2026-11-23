/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralSubtreeEmbeddings

/-!
# Single-Shape Fringe Laws and Aldous Concentration on Associahedra

This module develops the single-shape ("fringe") refinement of
`MathProject.AssociahedralSubtreeEmbeddings`, fixing a concrete pattern tree
`S : FullBracketing k` (`2 ≤ k`) rather than summing over all `k`-leaf shapes:

1. **Single-Shape Support & Equidistribution:**
   - `ShapeSupport T i S`: `[i, i + k)` forms a complete subtree of `T` isomorphic to `S`.
   - `operadicShapeEquiv`: equivalence
     `FullBracketing (N - k + 1) ≃ { T : FullBracketing N // ShapeSupport T i S }`,
     proving `subtree_shape_fiber_card` = `catalan (N - k)` (independent of `S`!).
   - `shapeCount T S`, `globalShapeMultiplicity N S = choose (2 * (N - k)) (N - k)`,
     `expectedShapeDensity N S`, and its asymptotic law `(1 / 4^(k-1)) * N + O(1)`.
2. **Single-Shape Second Moment, Variance, & Aldous Fringe Law Concentration:**
   - `operadicShapeTwoSiteEquiv`: two-site factorization for disjoint occurrences of `S`.
   - `globalShapePairMultiplicity N S`, `shapeSecondMoment N S`, `shapeVariance N S`,
     `shapeVariance_slope_pos`, `shapeVariance_sub_linear_tendsto`, `shapeVariance_div_tendsto`,
     and `shapeVariance_asymptotic` (`Var(n_S)(N) = O(N)`).
   - `shapeDensity_concentration_bound`, `shapeDensity_concentration_tendsto`, and
     `shape_universality_tendsto` (`ℙ(1 ≤ n_S(T)) → 1` as `N → ∞`).
   - `fringeMass_partialSum_tendsto`: `∑ k ∈ Finset.Ico 2 M, C_{k-1} / 4^(k-1) → 1` as `M → ∞`.
-/

namespace FunctorialGeometry

open Filter Topology Asymptotics

section SingleShapeEquidistribution

/-- Uniform `Fintype` instance on `FullBracketing n` for every `n : ℕ`. -/
@[instance_reducible]
private def instFintypeFullBracketingAll : (n : ℕ) → Fintype (FullBracketing n)
  | 0 => @Fintype.ofIsEmpty _ ⟨no_nullary_fullBracketing⟩
  | _ + 1 => inferInstance

attribute [local instance] instFintypeFullBracketingAll

private theorem fullBracketing_card_of_pos (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (FullBracketing n) = catalan (n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    rw [Nat.add_sub_cancel]
    convert fullBracketing_card m using 1

private theorem fullBracketing_nonempty_of_pos (N : ℕ) (hN : 1 ≤ N) :
    Nonempty (FullBracketing N) := by
  have hcb : 0 < Nat.centralBinom (N - 1) := Nat.centralBinom_pos (N - 1)
  have hcat : 0 < catalan (N - 1) := by
    by_contra h0
    have h0' : catalan (N - 1) = 0 := by omega
    have hmul := succ_mul_catalan_eq_centralBinom (N - 1)
    rw [h0', mul_zero] at hmul
    omega
  have hpos : 0 < Fintype.card (FullBracketing N) := by
    rw [fullBracketing_card_of_pos N hN]
    exact hcat
  exact Fintype.card_pos_iff.mp hpos

private theorem catalan_pos_of_nat (n : ℕ) : 0 < catalan n := by
  have hcb : 0 < Nat.centralBinom n := Nat.centralBinom_pos n
  by_contra h0
  have h0' : catalan n = 0 := by omega
  have hmul := succ_mul_catalan_eq_centralBinom n
  rw [h0', mul_zero] at hmul
  omega

/-- Contiguous interval `[i, i + k)` forms a complete sub-tree in `T` with exact shape `S`. -/
def ShapeSupport {N : ℕ} (T : FullBracketing N) (i : ℕ) {k : ℕ} (S : FullBracketing k) : Prop :=
  SubtreeSupport T i k ∧ extractAt T.val 0 i k = S.val

instance {N : ℕ} (T : FullBracketing N) (i : ℕ) {k : ℕ} (S : FullBracketing k) :
    Decidable (ShapeSupport T i S) :=
  inferInstanceAs (Decidable (SubtreeSupport T i k ∧ extractAt T.val 0 i k = S.val))

/-- **Single-Shape Operadic Factorization.**
Restricting `operadicFactorizationEquiv` to a fixed `k`-leaf shape `S` gives an explicit
equivalence `FullBracketing (N - k + 1) ≃ { T : FullBracketing N // ShapeSupport T i S }`. -/
def operadicShapeEquiv (N k i : ℕ) (hk : 2 ≤ k) (hi : i + k ≤ N) (S : FullBracketing k) :
    FullBracketing (N - k + 1) ≃ { T : FullBracketing N // ShapeSupport T i S } where
  toFun t_out :=
    let e := operadicFactorizationEquiv N k i hk hi
    let T := e (t_out, S)
    have hj : i < t_out.val.numLeaves := by rw [t_out.property]; omega
    have hkt : 2 ≤ S.val.numLeaves := by rw [S.property]; exact hk
    have hex : extractAt T.val.val 0 i k = S.val := by
      have h := extractAt_graftTree t_out.val S.val 0 i hj hkt
      change extractAt (graftTree t_out.val i S.val) 0 i k = S.val
      simpa only [Nat.zero_add, S.property] using h
    ⟨T.val, T.property, hex⟩
  invFun T :=
    let e := operadicFactorizationEquiv N k i hk hi
    (e.symm ⟨T.val, T.property.1⟩).1
  left_inv t_out := by
    let e := operadicFactorizationEquiv N k i hk hi
    exact congrArg Prod.fst (e.symm_apply_apply (t_out, S))
  right_inv T := by
    let e := operadicFactorizationEquiv N k i hk hi
    set p := e.symm ⟨T.val, T.property.1⟩
    have hp2 : p.2 = S := by
      apply Subtype.ext
      exact T.property.2
    have he : e (p.1, S) = ⟨T.val, T.property.1⟩ := by
      calc
        e (p.1, S) = e (p.1, p.2) := by rw [hp2]
        _ = e p := rfl
        _ = ⟨T.val, T.property.1⟩ := e.apply_symm_apply ⟨T.val, T.property.1⟩
    apply Subtype.ext
    dsimp only
    exact congrArg Subtype.val he

/-- **Single-Shape Equidistribution (Fiber Cardinality):**
For every fixed interval `[i, i + k)` (`2 ≤ k`, `i + k ≤ N`) and pattern `S : FullBracketing k`,
the number of trees `T ∈ FullBracketing N` with `ShapeSupport T i S` is `C_{N - k}`,
independent of both the position `i` and the shape `S`. -/
theorem subtree_shape_fiber_card (N k i : ℕ) (hk : 2 ≤ k) (hi : i + k ≤ N)
    (S : FullBracketing k) :
    Fintype.card { T : FullBracketing N // ShapeSupport T i S } = catalan (N - k) := by
  rw [Fintype.card_congr (operadicShapeEquiv N k i hk hi S).symm]
  rw [fullBracketing_card_of_pos (N - k + 1) (by omega), Nat.add_sub_cancel]

/-- Number of occurrences of the fixed fringe shape `S` as a complete sub-tree of `T`. -/
def shapeCount {N k : ℕ} (T : FullBracketing N) (S : FullBracketing k) : ℕ :=
  ((treeSpans T.val 0).filter
    (fun p => p.2 - p.1 = k ∧ extractAt T.val 0 p.1 k = S.val)).card

private theorem shapeCount_eq_card_intervals {N k : ℕ}
    (_hk : 2 ≤ k) (_hkN : k ≤ N) (T : FullBracketing N) (S : FullBracketing k) :
    shapeCount T S =
      ((Finset.univ : Finset (Fin (N - k + 1))).filter
        (fun i => ShapeSupport T i.val S)).card := by
  dsimp [shapeCount]
  symm
  refine Finset.card_nbij (fun i => (i.val, i.val + k)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, by omega, hi.2⟩
  · intro a _ b _ hab
    ext
    exact congrArg Prod.fst hab
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    have hv := treeSpans_valid T.val 0 p hp.1
    rw [T.property] at hv
    dsimp [SpanValid] at hv
    refine ⟨⟨p.1, by omega⟩, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hp2 : p.1 + k = p.2 := by omega
      have hpair : (p.1, p.1 + k) = p := Prod.ext rfl hp2
      refine ⟨?_, hp.2.2⟩
      change (p.1, p.1 + k) ∈ treeSpans T.val 0
      rw [hpair]
      exact hp.1
    · change (p.1, p.1 + k) = p
      exact Prod.ext rfl (by omega)

/-- Total number of occurrences of the fixed shape `S` across all trees in `FullBracketing N`,
summed over all contiguous intervals `i : Fin (N - k + 1)`. -/
def globalShapeMultiplicity (N : ℕ) {k : ℕ} (S : FullBracketing k) : ℕ :=
  ∑ i : Fin (N - k + 1), Fintype.card { T : FullBracketing N // ShapeSupport T i.val S }

/-- Double counting: summing single-shape fiber cardinalities over intervals equals summing
`shapeCount T S` over all trees `T : FullBracketing N`. -/
theorem globalShapeMultiplicity_eq_tree_sum (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) :
    globalShapeMultiplicity N S = ∑ T : FullBracketing N, shapeCount T S := by
  dsimp [globalShapeMultiplicity]
  have hcard : ∀ i : Fin (N - k + 1),
      Fintype.card { T : FullBracketing N // ShapeSupport T i.val S } =
        ∑ T : FullBracketing N, if ShapeSupport T i.val S then 1 else 0 := by
    intro i
    rw [Fintype.card_subtype, Finset.card_filter]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_boole, Nat.cast_id, ← shapeCount_eq_card_intervals hk hkN T S]

/-- **Global Single-Shape Multiplicity:**
For `2 ≤ k ≤ N` and any `S : FullBracketing k`,
`Φ_S(N) = choose (2 * (N - k)) (N - k)`. -/
theorem globalShapeMultiplicity_eq (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) :
    globalShapeMultiplicity N S = Nat.choose (2 * (N - k)) (N - k) := by
  dsimp [globalShapeMultiplicity]
  have hterm : ∀ i : Fin (N - k + 1),
      Fintype.card { T : FullBracketing N // ShapeSupport T i.val S } = catalan (N - k) :=
    fun i => subtree_shape_fiber_card N k i.val hk (by omega) S
  simp_rw [hterm, Finset.sum_const, Finset.card_fin, smul_eq_mul]
  rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]

private theorem globalSubtreeMultiplicity_eq_mul_shape (N : ℕ) {k : ℕ} (hk : 2 ≤ k)
    (hkN : k ≤ N) (S : FullBracketing k) :
    globalSubtreeMultiplicity N k = catalan (k - 1) * globalShapeMultiplicity N S := by
  rw [globalSubtreeMultiplicity_eq N k hk hkN, globalShapeMultiplicity_eq N hk hkN S]

/-- Expected number of occurrences of the fixed fringe shape `S` in a uniform random tree
`T ∈ FullBracketing N`. -/
noncomputable def expectedShapeDensity (N : ℕ) {k : ℕ} (S : FullBracketing k) : ℝ :=
  (globalShapeMultiplicity N S : ℝ) / (Fintype.card (FullBracketing N) : ℝ)

theorem expectedShapeDensity_eq_tree_avg (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) :
    expectedShapeDensity N S =
      (∑ T : FullBracketing N, (shapeCount T S : ℝ)) /
        (Fintype.card (FullBracketing N) : ℝ) := by
  dsimp [expectedShapeDensity]
  rw [globalShapeMultiplicity_eq_tree_sum N hk hkN S]
  push_cast
  rfl

local instance (N : ℕ) : MeasurableSpace (FullBracketing N) := ⊤

theorem expectedShapeDensity_eq_uniform_expectation (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) [Nonempty (FullBracketing N)] :
    expectedShapeDensity N S =
      ∑ T : FullBracketing N,
        (MeasureTheory.Measure.uniformOfFinset
          (Finset.univ : Finset (FullBracketing N)) {T}).toReal * (shapeCount T S : ℝ) := by
  rw [expectedShapeDensity_eq_tree_avg N hk hkN S]
  simp only [MeasureTheory.Measure.uniformOfFinset_apply_singleton, Finset.mem_univ, ↓reduceIte,
    Finset.card_univ, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← Finset.mul_sum, div_eq_inv_mul]

/-- **Exact Expected Single-Shape Density:**
For `2 ≤ k ≤ N` and any `S : FullBracketing k`,
`E[n_S](N) = choose (2 * (N - k)) (N - k) / (choose (2 * (N - 1)) (N - 1) / N)`. -/
theorem expectedShapeDensity_eq (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) :
    expectedShapeDensity N S =
      (Nat.choose (2 * (N - k)) (N - k) : ℝ) /
        ((Nat.choose (2 * (N - 1)) (N - 1) : ℝ) / (N : ℝ)) := by
  have hN : 1 ≤ N := by omega
  dsimp [expectedShapeDensity]
  rw [globalShapeMultiplicity_eq N hk hkN S, fullBracketing_card_of_pos N hN]
  have hcat : (catalan (N - 1) : ℝ) = (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) / (N : ℝ) := by
    have hmul : N * catalan (N - 1) = Nat.choose (2 * (N - 1)) (N - 1) := by
      have h := succ_mul_catalan_eq_centralBinom (N - 1)
      rw [Nat.sub_add_cancel hN, Nat.centralBinom_eq_two_mul_choose] at h
      exact h
    have hNpos : (N : ℝ) ≠ 0 := by positivity
    have hmulR : (N : ℝ) * (catalan (N - 1) : ℝ) = (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) := by
      exact_mod_cast hmul
    field_simp [hNpos]
    linarith
  rw [hcat]

private theorem expectedSubtreeDensity_eq_mul_shape (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) :
    expectedSubtreeDensity N k = (catalan (k - 1) : ℝ) * expectedShapeDensity N S := by
  rw [expectedSubtreeDensity_eq N k hk hkN, expectedShapeDensity_eq N hk hkN S]
  ring

/-- **Single-Shape Asymptotic Constant Limit:**
For fixed `k ≥ 2` and `S : FullBracketing k`,
`E[n_S](N) - (1 / 4^(k-1)) * N → (k - 1) / (2 * 4^(k-1))` as `N → ∞`. -/
theorem expectedShapeDensity_sub_linear_tendsto {k : ℕ} (hk : 2 ≤ k)
    (S : FullBracketing k) :
    Tendsto
      (fun N : ℕ => expectedShapeDensity N S - ((1 : ℝ) / 4 ^ (k - 1)) * (N : ℝ))
      atTop (𝓝 (((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1)))) := by
  have hc_pos : (0 : ℝ) < (catalan (k - 1) : ℝ) := by
    exact_mod_cast catalan_pos_of_nat (k - 1)
  have hc_ne : (catalan (k - 1) : ℝ) ≠ 0 := ne_of_gt hc_pos
  have hsub := (expectedSubtreeDensity_sub_linear_tendsto k hk).div_const (catalan (k - 1) : ℝ)
  have hlim :
      ((catalan (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1))) / (catalan (k - 1) : ℝ) =
        ((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1)) := by
    field_simp [hc_ne]
  rw [hlim] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  rw [expectedSubtreeDensity_eq_mul_shape N hk hN S]
  field_simp [hc_ne]

/-- **Single-Shape Asymptotic Law (`O(1)` Remainder):**
For fixed `k ≥ 2` and `S : FullBracketing k`,
`E[n_S](N) - (1 / 4^(k-1)) * N = O(1)` as `N → ∞`. -/
theorem expectedShapeDensity_asymptotic {k : ℕ} (hk : 2 ≤ k) (S : FullBracketing k) :
    (fun N : ℕ => expectedShapeDensity N S - ((1 : ℝ) / 4 ^ (k - 1)) * (N : ℝ))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
  (expectedShapeDensity_sub_linear_tendsto hk S).isBigO_one ℝ

/-- **Exact `O(1 / N)` Single-Shape Remainder Bound:**
`E[n_S](N) - (1 / 4^(k-1)) * N - (k - 1) / (2 * 4^(k-1)) = O(1 / N)`. -/
theorem expectedShapeDensity_asymptotic_inv {k : ℕ} (hk : 2 ≤ k) (S : FullBracketing k) :
    (fun N : ℕ =>
      expectedShapeDensity N S -
        ((1 : ℝ) / 4 ^ (k - 1)) * (N : ℝ) -
        ((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1)))
      =O[atTop] (fun N : ℕ => (1 : ℝ) / (N : ℝ)) := by
  have hc_pos : (0 : ℝ) < (catalan (k - 1) : ℝ) := by
    exact_mod_cast catalan_pos_of_nat (k - 1)
  have hc_ne : (catalan (k - 1) : ℝ) ≠ 0 := ne_of_gt hc_pos
  have hbig := (expectedSubtreeDensity_asymptotic_inv k hk).const_mul_left
    ((catalan (k - 1) : ℝ)⁻¹)
  refine hbig.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop k] with N hN
  rw [expectedSubtreeDensity_eq_mul_shape N hk hN S]
  field_simp [hc_ne]

end SingleShapeEquidistribution

section FringeVarianceAndConcentration

attribute [local instance] instFintypeFullBracketingAll

private theorem extractAt_graftTree_of_le (t_out t_in : BinaryTree Unit) (start j i k : ℕ)
    (hj : j < t_out.numLeaves) (hk_in : 2 ≤ t_in.numLeaves) (hk : 2 ≤ k)
    (hik : i + k ≤ start + j) (hmem : (i, i + k) ∈ treeSpans t_out start) :
    extractAt (graftTree t_out j t_in) start i k = extractAt t_out start i k := by
  induction t_out generalizing start j with
  | nil => simp [treeSpans] at hmem
  | node val l r il ir =>
    cases val
    simp only [BinaryTree.numLeaves] at hj
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hmem
    have hnroot_out : ¬ (i = start ∧ i + k = start + l.numLeaves + r.numLeaves) := by omega
    dsimp [graftTree]
    split_ifs with h
    · have hgl := graftTree_numLeaves l t_in j h
      have hnroot_in :
          ¬ (i = start ∧ i + k = start + (graftTree l j t_in).numLeaves + r.numLeaves) := by
        omega
      have hlmem : (i, i + k) ∈ treeSpans l start := by
        rcases hmem with hroot | hlmem | hrmem
        · obtain ⟨h1, h2⟩ := Prod.mk.inj hroot
          omega
        · exact hlmem
        · have hv := treeSpans_valid r (start + l.numLeaves) _ hrmem
          dsimp [SpanValid] at hv
          omega
      dsimp [extractAt]
      rw [ite_eq_right hnroot_in, ite_eq_left (by omega)]
      rw [ite_eq_right hnroot_out, ite_eq_left (by omega)]
      exact il start j h (by omega) hlmem
    · have hgr := graftTree_numLeaves r t_in (j - l.numLeaves) (by omega)
      have hnroot_in :
          ¬ (i = start ∧
            i + k = start + l.numLeaves + (graftTree r (j - l.numLeaves) t_in).numLeaves) := by
        omega
      dsimp [extractAt]
      rw [ite_eq_right hnroot_in, ite_eq_right hnroot_out]
      by_cases hle : i + k ≤ start + l.numLeaves
      · rw [ite_eq_left hle, ite_eq_left hle]
      · rw [ite_eq_right hle, ite_eq_right hle]
        have hrmem : (i, i + k) ∈ treeSpans r (start + l.numLeaves) := by
          rcases hmem with hroot | hlmem | hrmem
          · obtain ⟨h1, h2⟩ := Prod.mk.inj hroot
            omega
          · have hv := treeSpans_valid l start _ hlmem
            dsimp [SpanValid] at hv
            omega
          · exact hrmem
        exact ir (start + l.numLeaves) (j - l.numLeaves) (by omega) (by omega) hrmem

/-- **Two-Site Single-Shape Operadic Factorization.**
Restricting `operadicTwoSiteEquiv` to two disjoint occurrences of the same shape `S` gives
`FullBracketing (N - 2 * k + 2) ≃`
`{ T : FullBracketing N // ShapeSupport T i S ∧ ShapeSupport T j S }`. -/
def operadicShapeTwoSiteEquiv (N k i j : ℕ) (hk : 2 ≤ k) (hij : i + k ≤ j)
    (hj : j + k ≤ N) (S : FullBracketing k) :
    FullBracketing (N - 2 * k + 2) ≃
      { T : FullBracketing N // ShapeSupport T i S ∧ ShapeSupport T j S } where
  toFun t_out :=
    let e2 := operadicTwoSiteEquiv N k i j hk hij hj
    let eI := operadicFactorizationEquiv (N - k + 1) k i hk (by omega)
    let eJ := operadicFactorizationEquiv N k j hk hj
    let t_cast : FullBracketing (N - k + 1 - k + 1) :=
      Equiv.cast (by congr 1; omega) t_out
    let T' := eI (t_cast, S)
    let T := eJ (T'.val, S)
    have hT_eq : (e2 (t_out, S, S)).val = T.val := rfl
    have hj_out : j < T'.val.val.numLeaves := by rw [T'.val.property]; omega
    have hi_out : i < t_cast.val.numLeaves := by rw [t_cast.property]; omega
    have hkt : 2 ≤ S.val.numLeaves := by rw [S.property]; exact hk
    have hexJ : extractAt T.val.val 0 j k = S.val := by
      have h := extractAt_graftTree T'.val.val S.val 0 j hj_out hkt
      change extractAt (graftTree T'.val.val j S.val) 0 j k = S.val
      simpa only [Nat.zero_add, S.property] using h
    have hexI' : extractAt T'.val.val 0 i k = S.val := by
      have h := extractAt_graftTree t_cast.val S.val 0 i hi_out hkt
      change extractAt (graftTree t_cast.val i S.val) 0 i k = S.val
      simpa only [Nat.zero_add, S.property] using h
    have hexI : extractAt T.val.val 0 i k = S.val := by
      have h := extractAt_graftTree_of_le T'.val.val S.val 0 j i k hj_out hkt hk
        (by omega) T'.property
      change extractAt (graftTree T'.val.val j S.val) 0 i k = extractAt T'.val.val 0 i k at h
      change extractAt (graftTree T'.val.val j S.val) 0 i k = S.val
      rw [h, hexI']
    have hsup := (e2 (t_out, S, S)).property
    ⟨(e2 (t_out, S, S)).val, ⟨hsup.1, by rw [hT_eq]; exact hexI⟩,
      ⟨hsup.2, by rw [hT_eq]; exact hexJ⟩⟩
  invFun T :=
    ((operadicTwoSiteEquiv N k i j hk hij hj).symm ⟨T.val, T.property.1.1, T.property.2.1⟩).1
  left_inv t_out := by
    let e2 := operadicTwoSiteEquiv N k i j hk hij hj
    exact congrArg Prod.fst (e2.symm_apply_apply (t_out, S, S))
  right_inv T := by
    let e2 := operadicTwoSiteEquiv N k i j hk hij hj
    let eI := operadicFactorizationEquiv (N - k + 1) k i hk (by omega)
    let eJ := operadicFactorizationEquiv N k j hk hj
    set p := e2.symm ⟨T.val, T.property.1.1, T.property.2.1⟩
    let t_cast : FullBracketing (N - k + 1 - k + 1) :=
      Equiv.cast (by congr 1; omega) p.1
    let T' := eI (t_cast, p.2.1)
    have happly : e2 p = ⟨T.val, T.property.1.1, T.property.2.1⟩ :=
      e2.apply_symm_apply ⟨T.val, T.property.1.1, T.property.2.1⟩
    have hJ_val : (eJ (T'.val, p.2.2)).val = T.val := congrArg Subtype.val happly
    have hJ_eq : eJ (T'.val, p.2.2) = ⟨T.val, T.property.2.1⟩ := Subtype.ext hJ_val
    have hJ_symm : (T'.val, p.2.2) = eJ.symm ⟨T.val, T.property.2.1⟩ := by
      rw [← hJ_eq, eJ.symm_apply_apply]
    have hp22 : p.2.2 = S := by
      have h2 := congrArg Prod.snd hJ_symm
      dsimp at h2
      rw [h2]
      apply Subtype.ext
      exact T.property.2.2
    have hi_T' : SubtreeSupport T'.val i k := T'.property
    have hex_T' : extractAt T'.val.val 0 i k = S.val := by
      have h := extractAt_graftTree_of_le T'.val.val p.2.2.val 0 j i k
        (by rw [T'.val.property]; omega) (by rw [p.2.2.property]; exact hk) hk
        (by omega) hi_T'
      change extractAt (eJ (T'.val, p.2.2)).val.val 0 i k = extractAt T'.val.val 0 i k at h
      rw [hJ_val] at h
      rw [← h]
      exact T.property.1.2
    have hp21 : p.2.1 = S := by
      have hI_symm : (t_cast, p.2.1) = eI.symm T' := (eI.symm_apply_apply (t_cast, p.2.1)).symm
      have h2 := congrArg Prod.snd hI_symm
      dsimp at h2
      rw [h2]
      apply Subtype.ext
      exact hex_T'
    have hp_eq : (p.1, S, S) = p := by
      ext1
      · rfl
      · exact Prod.ext hp21.symm hp22.symm
    have he2 : (e2 (p.1, S, S)).val = T.val := by
      rw [hp_eq]
      exact congrArg Subtype.val happly
    apply Subtype.ext
    exact he2

/-- **Two-Site Single-Shape Fiber Cardinality:**
For disjoint intervals `[i, i + k)` and `[j, j + k)` with `i + k ≤ j` and `j + k ≤ N`,
the number of trees `T ∈ FullBracketing N` with `ShapeSupport T i S ∧ ShapeSupport T j S`
is `C_{N - 2k + 1}`. -/
theorem shape_two_site_fiber_card (N k i j : ℕ) (hk : 2 ≤ k) (hij : i + k ≤ j)
    (hj : j + k ≤ N) (S : FullBracketing k) :
    Fintype.card { T : FullBracketing N // ShapeSupport T i S ∧ ShapeSupport T j S } =
      catalan (N - 2 * k + 1) := by
  rw [Fintype.card_congr (operadicShapeTwoSiteEquiv N k i j hk hij hj S).symm]
  rw [fullBracketing_card_of_pos (N - 2 * k + 2) (by omega)]
  have hsub : N - 2 * k + 2 - 1 = N - 2 * k + 1 := by omega
  rw [hsub]

theorem shape_disjoint_fiber_card (N k i j : ℕ) (hk : 2 ≤ k)
    (hi : i + k ≤ N) (hj : j + k ≤ N) (hdisj : i + k ≤ j ∨ j + k ≤ i)
    (S : FullBracketing k) :
    Fintype.card { T : FullBracketing N // ShapeSupport T i S ∧ ShapeSupport T j S } =
      catalan (N - 2 * k + 1) := by
  rcases hdisj with hij | hji
  · exact shape_two_site_fiber_card N k i j hk hij hj S
  · have hswap :
        { T : FullBracketing N // ShapeSupport T i S ∧ ShapeSupport T j S } ≃
          { T : FullBracketing N // ShapeSupport T j S ∧ ShapeSupport T i S } :=
      Equiv.subtypeEquivRight (fun _ => and_comm)
    rw [Fintype.card_congr hswap]
    exact shape_two_site_fiber_card N k j i hk hji hi S

/-- Total number of ordered pairs of distinct occurrences of the fixed shape `S` across all
trees in `FullBracketing N`. -/
def globalShapePairMultiplicity (N : ℕ) {k : ℕ} (S : FullBracketing k) : ℕ :=
  ∑ T : FullBracketing N, shapeCount T S * (shapeCount T S - 1)

/-- When `N < 2 * k`, no tree can contain two distinct occurrences of a `k`-leaf shape `S`. -/
theorem globalShapePairMultiplicity_eq_zero_of_lt (N : ℕ) {k : ℕ} (_hk : 2 ≤ k)
    (hNk : N < 2 * k) (S : FullBracketing k) :
    globalShapePairMultiplicity N S = 0 := by
  dsimp [globalShapePairMultiplicity]
  refine Finset.sum_eq_zero fun T _ => ?_
  have hle : shapeCount T S ≤ 1 := by
    dsimp [shapeCount]
    by_contra hgt
    have h1 :
        1 < ((treeSpans T.val 0).filter
          (fun p => p.2 - p.1 = k ∧ extractAt T.val 0 p.1 k = S.val)).card := by
      omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
    simp only [Finset.mem_filter] at hp hq
    have vp := treeSpans_valid T.val 0 p hp.1
    have vq := treeSpans_valid T.val 0 q hq.1
    rw [T.property] at vp vq
    dsimp [SpanValid] at vp vq
    have hcomp := treeSpans_compatible T.val 0 p hp.1 q hq.1
    dsimp [SpanCompatible] at hcomp
    have hne : p.1 ≠ q.1 := by
      intro heq
      apply hpq
      exact Prod.ext heq (by omega)
    omega
  have hsub : shapeCount T S - 1 = 0 := by omega
  rw [hsub, mul_zero]

private theorem disjoint_interval_pairs_card (N k : ℕ) (_hk : 2 ≤ k) (hkN : 2 * k ≤ N) :
    ((Finset.univ : Finset (Fin (N - k + 1) × Fin (N - k + 1))).filter
      (fun p => p.1.val + k ≤ p.2.val ∨ p.2.val + k ≤ p.1.val)).card =
      (N - 2 * k + 2) * (N - 2 * k + 1) := by
  have hoff : (Finset.univ : Finset (Fin (N - 2 * k + 2))).offDiag.card =
      (N - 2 * k + 2) * (N - 2 * k + 1) := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    have h1 : N - 2 * k + 2 - 1 = N - 2 * k + 1 := by omega
    rw [← h1, Nat.mul_sub_one]
  rw [← hoff]
  symm
  refine Finset.card_nbij
    (fun q : Fin (N - 2 * k + 2) × Fin (N - 2 * k + 2) =>
      if q.1.val < q.2.val then
        (⟨q.1.val, by omega⟩, ⟨q.2.val + k - 1, by omega⟩)
      else
        (⟨q.1.val + k - 1, by omega⟩, ⟨q.2.val, by omega⟩)) ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_offDiag, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · left; dsimp; omega
    · right; dsimp; have hlt : q.2.val < q.1.val := by
        exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm (Fin.val_ne_of_ne hq))
      omega
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_offDiag, Finset.mem_univ, true_and] at ha hb
    dsimp only at hab
    split_ifs at hab with ha1 hb1 <;>
      have h1 := congrArg (fun x : Fin (N - k + 1) × Fin (N - k + 1) => x.1.val) hab <;>
      have h2 := congrArg (fun x : Fin (N - k + 1) × Fin (N - k + 1) => x.2.val) hab <;>
      dsimp at h1 h2
    · ext <;> omega
    · have : b.2.val < b.1.val := lt_of_le_of_ne (not_lt.mp hb1) (Ne.symm (Fin.val_ne_of_ne hb))
      omega
    · have : a.2.val < a.1.val := lt_of_le_of_ne (not_lt.mp ha1) (Ne.symm (Fin.val_ne_of_ne ha))
      omega
    · ext <;> omega
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with hij | hji
    · refine ⟨(⟨p.1.val, by omega⟩, ⟨p.2.val - (k - 1), by omega⟩), ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_offDiag, Finset.mem_univ, true_and]
        intro heq
        have hv := congrArg Fin.val heq
        dsimp at hv
        omega
      · dsimp only
        rw [ite_eq_left (by omega)]
        exact Prod.ext (Fin.ext rfl) (Fin.ext (by dsimp; omega))
    · refine ⟨(⟨p.1.val - (k - 1), by omega⟩, ⟨p.2.val, by omega⟩), ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_offDiag, Finset.mem_univ, true_and]
        intro heq
        have hv := congrArg Fin.val heq
        dsimp at hv
        omega
      · dsimp only
        rw [ite_eq_right (by omega)]
        exact Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext rfl)

/-- **Second Factorial Single-Shape Multiplicity:**
For `2 * k ≤ N` and any `S : FullBracketing k`,
`Φ₂_S(N) = (N - 2k + 1) * choose (2 * (N - 2k + 1)) (N - 2k + 1)`. -/
theorem globalShapePairMultiplicity_eq (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : 2 * k ≤ N)
    (S : FullBracketing k) :
    globalShapePairMultiplicity N S =
      (N - 2 * k + 1) * Nat.choose (2 * (N - 2 * k + 1)) (N - 2 * k + 1) := by
  dsimp [globalShapePairMultiplicity]
  have htree : ∀ T : FullBracketing N,
      shapeCount T S * (shapeCount T S - 1) =
        ∑ p ∈ (Finset.univ : Finset (Fin (N - k + 1) × Fin (N - k + 1))).filter
          (fun p => p.1.val + k ≤ p.2.val ∨ p.2.val + k ≤ p.1.val),
          if ShapeSupport T p.1.val S ∧ ShapeSupport T p.2.val S then 1 else 0 := by
    intro T
    rw [shapeCount_eq_card_intervals hk (by omega) T S]
    set I := (Finset.univ : Finset (Fin (N - k + 1))).filter (fun i => ShapeSupport T i.val S)
    rw [Nat.mul_sub_one, ← Finset.offDiag_card]
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    have hsplit : I.offDiag =
        ((Finset.univ : Finset (Fin (N - k + 1) × Fin (N - k + 1))).filter
          (fun p => p.1.val + k ≤ p.2.val ∨ p.2.val + k ≤ p.1.val)).filter
          (fun p => ShapeSupport T p.1.val S ∧ ShapeSupport T p.2.val S) := by
      ext p
      simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and, I]
      constructor
      · rintro ⟨hp1, hp2, hne⟩
        refine ⟨?_, hp1, hp2⟩
        exact subtreeSupport_disjoint_of_ne hk (fun hv => hne (Fin.ext hv)) hp1.1 hp2.1
      · rintro ⟨_, hp1, hp2⟩
        refine ⟨hp1, hp2, ?_⟩
        intro heq
        have hv := congrArg Fin.val heq
        omega
    rw [hsplit, Finset.sum_filter]
  simp_rw [htree]
  rw [Finset.sum_comm]
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin (N - k + 1) × Fin (N - k + 1))).filter
      (fun p => p.1.val + k ≤ p.2.val ∨ p.2.val + k ≤ p.1.val),
      (∑ T : FullBracketing N,
        if ShapeSupport T p.1.val S ∧ ShapeSupport T p.2.val S then 1 else 0) =
        catalan (N - 2 * k + 1) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [← Finset.card_filter, ← Fintype.card_subtype]
    exact shape_disjoint_fiber_card N k p.1.val p.2.val hk (by omega) (by omega) hp S
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  rw [disjoint_interval_pairs_card N k hk hkN]
  calc
    (N - 2 * k + 2) * (N - 2 * k + 1) * catalan (N - 2 * k + 1)
      = (N - 2 * k + 1) * ((N - 2 * k + 2) * catalan (N - 2 * k + 1)) := by ring
    _ = (N - 2 * k + 1) * (N - 2 * k + 1).centralBinom := by
        rw [succ_mul_catalan_eq_centralBinom]
    _ = (N - 2 * k + 1) * Nat.choose (2 * (N - 2 * k + 1)) (N - 2 * k + 1) := by
        rw [Nat.centralBinom_eq_two_mul_choose]

private theorem globalSubtreePairMultiplicity_eq_mul_shape (N : ℕ) {k : ℕ} (hk : 2 ≤ k)
    (_hkN : k ≤ N) (S : FullBracketing k) :
    globalSubtreePairMultiplicity N k = catalan (k - 1) ^ 2 * globalShapePairMultiplicity N S := by
  by_cases h2k : 2 * k ≤ N
  · rw [globalSubtreePairMultiplicity_eq N k hk h2k,
      globalShapePairMultiplicity_eq N hk h2k S]
    ring
  · have hlt : N < 2 * k := by omega
    rw [globalSubtreePairMultiplicity_eq_zero_of_lt N k hk hlt,
      globalShapePairMultiplicity_eq_zero_of_lt N hk hlt S, mul_zero]

/-- Second moment `E[n_S^2](N)` of the single-shape count `shapeCount T S` under the uniform
distribution on `FullBracketing N`. -/
noncomputable def shapeSecondMoment (N : ℕ) {k : ℕ} (S : FullBracketing k) : ℝ :=
  (∑ T : FullBracketing N, (shapeCount T S : ℝ) ^ 2) /
    (Fintype.card (FullBracketing N) : ℝ)

/-- Variance `Var(n_S)(N) = E[n_S^2](N) - E[n_S](N)^2`. -/
noncomputable def shapeVariance (N : ℕ) {k : ℕ} (S : FullBracketing k) : ℝ :=
  shapeSecondMoment N S - expectedShapeDensity N S ^ 2

private theorem shapeSecondMoment_eq_pair_add_avg (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) :
    shapeSecondMoment N S =
      (globalShapePairMultiplicity N S : ℝ) / (Fintype.card (FullBracketing N) : ℝ) +
        expectedShapeDensity N S := by
  have hsq : ∀ T : FullBracketing N,
      (shapeCount T S : ℝ) ^ 2 =
        ((shapeCount T S * (shapeCount T S - 1) : ℕ) : ℝ) + (shapeCount T S : ℝ) := by
    intro T
    set c := shapeCount T S
    have hc : c * c = c * (c - 1) + c := by
      cases c with
      | zero => simp
      | succ m =>
        simp only [Nat.add_sub_cancel]
        ring
    have hc' : (c : ℝ) * (c : ℝ) = ((c * (c - 1) : ℕ) : ℝ) + (c : ℝ) := by exact_mod_cast hc
    simpa [sq] using hc'
  dsimp [shapeSecondMoment]
  simp_rw [hsq, Finset.sum_add_distrib, add_div]
  rw [← expectedShapeDensity_eq_tree_avg N hk hkN S]
  congr 1
  norm_cast

private theorem subtreeSecondMoment_eq_pair_add_avg (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) :
    subtreeSecondMoment N k =
      (globalSubtreePairMultiplicity N k : ℝ) / (Fintype.card (FullBracketing N) : ℝ) +
        expectedSubtreeDensity N k := by
  have hsq : ∀ T : FullBracketing N,
      (((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card : ℝ) ^ 2 =
        ((((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card *
          (((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card - 1) : ℕ) : ℝ) +
          (((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card : ℝ) := by
    intro T
    set c := ((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card
    have hc : c * c = c * (c - 1) + c := by
      cases c with
      | zero => simp
      | succ m =>
        simp only [Nat.add_sub_cancel]
        ring
    have hc' : (c : ℝ) * (c : ℝ) = ((c * (c - 1) : ℕ) : ℝ) + (c : ℝ) := by exact_mod_cast hc
    simpa [sq] using hc'
  have hpair :
      (∑ T : FullBracketing N,
        ((((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card *
          (((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card - 1) : ℕ) : ℝ)) =
        (globalSubtreePairMultiplicity N k : ℝ) := by
    dsimp [globalSubtreePairMultiplicity]
    norm_cast
  have hlhs :
      subtreeSecondMoment N k =
        (∑ T : FullBracketing N,
          (((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card : ℝ) ^ 2) /
          (Fintype.card (FullBracketing N) : ℝ) := by
    dsimp [subtreeSecondMoment]
    congr
  have havg :
      expectedSubtreeDensity N k =
        (∑ T : FullBracketing N,
          (((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card : ℝ)) /
          (Fintype.card (FullBracketing N) : ℝ) := by
    rw [expectedSubtreeDensity_eq_tree_avg N k hk hkN]
    congr
  rw [hlhs]
  simp_rw [hsq, Finset.sum_add_distrib, add_div, hpair, ← havg]

/-- **Closed-Form Second Moment `E[n_S^2](N)`:**
For `2 * k ≤ N`, expressed via central binomial ratios and `expectedShapeDensity N S`. -/
theorem shapeSecondMoment_eq (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : 2 * k ≤ N)
    (S : FullBracketing k) :
    shapeSecondMoment N S =
      (N : ℝ) * ((N : ℝ) - 2 * (k : ℝ) + 1) *
        ((Nat.choose (2 * (N - (2 * k - 1))) (N - (2 * k - 1)) : ℝ) /
          (Nat.choose (2 * (N - 1)) (N - 1) : ℝ)) +
        expectedShapeDensity N S := by
  have hN : 1 ≤ N := by omega
  rw [shapeSecondMoment_eq_pair_add_avg N hk (by omega) S]
  rw [globalShapePairMultiplicity_eq N hk hkN S, fullBracketing_card_of_pos N hN]
  have hcat : (catalan (N - 1) : ℝ) = (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) / (N : ℝ) := by
    have hmul : N * catalan (N - 1) = Nat.choose (2 * (N - 1)) (N - 1) := by
      have h := succ_mul_catalan_eq_centralBinom (N - 1)
      rw [Nat.sub_add_cancel hN, Nat.centralBinom_eq_two_mul_choose] at h
      exact h
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hmulR : (N : ℝ) * (catalan (N - 1) : ℝ) = (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) := by
      exact_mod_cast hmul
    field_simp [hN0]
    linarith
  have hsub1 : (N - 2 * k + 1 : ℕ) = N - (2 * k - 1) := by omega
  have hsubR : ((N - 2 * k + 1 : ℕ) : ℝ) = (N : ℝ) - 2 * (k : ℝ) + 1 := by
    have hnat : N + 1 = (N - 2 * k + 1) + 2 * k := by omega
    have hcast : (N : ℝ) + 1 = ((N - 2 * k + 1 : ℕ) : ℝ) + 2 * (k : ℝ) := by
      exact_mod_cast hnat
    linarith
  rw [hcat, Nat.cast_mul, hsub1, ← hsub1, hsubR]
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hden : (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) ≠ 0 := by
    rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero (N - 1))
  field_simp [hN0, hden]

/-- Centered-square expression for `shapeVariance N S`. -/
theorem shapeVariance_eq_sum_sq_sub (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) :
    shapeVariance N S =
      (∑ T : FullBracketing N, ((shapeCount T S : ℝ) - expectedShapeDensity N S) ^ 2) /
        (Fintype.card (FullBracketing N) : ℝ) := by
  have hN : 1 ≤ N := by omega
  have _ : Nonempty (FullBracketing N) := fullBracketing_nonempty_of_pos N hN
  have hcard : (Fintype.card (FullBracketing N) : ℝ) ≠ 0 := by positivity
  have havg := expectedShapeDensity_eq_tree_avg N hk hkN S
  have hsum :
      (∑ T : FullBracketing N, (shapeCount T S : ℝ)) =
        (Fintype.card (FullBracketing N) : ℝ) * expectedShapeDensity N S := by
    rw [havg]
    field_simp [hcard]
  dsimp [shapeVariance, shapeSecondMoment]
  have hexp :
      (∑ T : FullBracketing N, ((shapeCount T S : ℝ) - expectedShapeDensity N S) ^ 2) =
        (∑ T : FullBracketing N, (shapeCount T S : ℝ) ^ 2) -
          2 * expectedShapeDensity N S * (∑ T : FullBracketing N, (shapeCount T S : ℝ)) +
          (Fintype.card (FullBracketing N) : ℝ) * expectedShapeDensity N S ^ 2 := by
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hmid :
        (∑ T : FullBracketing N,
          2 * (shapeCount T S : ℝ) * expectedShapeDensity N S) =
          2 * expectedShapeDensity N S * (∑ T : FullBracketing N, (shapeCount T S : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => by ring
    rw [hmid]
  rw [hexp, hsum]
  field_simp [hcard]
  ring

theorem shapeVariance_nonneg (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) :
    0 ≤ shapeVariance N S := by
  rw [shapeVariance_eq_sum_sq_sub N hk hkN S]
  refine div_nonneg (Finset.sum_nonneg fun T _ => sq_nonneg _) (Nat.cast_nonneg _)

local instance (N : ℕ) : MeasurableSpace (FullBracketing N) := ⊤

/-- Uniform probability expectation form of the single-shape variance `Var(n_S)(N)`. -/
theorem shapeVariance_eq_uniform_expectation (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) [Nonempty (FullBracketing N)] :
    shapeVariance N S =
      ∑ T : FullBracketing N,
        (MeasureTheory.Measure.uniformOfFinset
          (Finset.univ : Finset (FullBracketing N)) {T}).toReal *
          ((shapeCount T S : ℝ) - expectedShapeDensity N S) ^ 2 := by
  rw [shapeVariance_eq_sum_sq_sub N hk hkN S]
  simp only [MeasureTheory.Measure.uniformOfFinset_apply_singleton, Finset.mem_univ, ↓reduceIte,
    Finset.card_univ, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← Finset.mul_sum, div_eq_inv_mul]

/-- **Positivity of the Single-Shape Variance Slope:**
For every `k ≥ 2`, `q_k - (2k - 1) * q_k^2 > 0`, where `q_k = 1 / 4^(k-1)`. -/
theorem shapeVariance_slope_pos (k : ℕ) (hk : 2 ≤ k) :
    0 < (1 : ℝ) / 4 ^ (k - 1) - (2 * (k : ℝ) - 1) * ((1 : ℝ) / 4 ^ (k - 1)) ^ 2 := by
  have hlt : 2 * k - 1 < 4 ^ (k - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
    induction m with
    | zero => decide
    | succ m ih =>
      have hih := ih
      have hsub1 : m + 2 + 1 - 1 = (m + 2 - 1) + 1 := by omega
      rw [hsub1, pow_succ]
      omega
  have hltR : 2 * (k : ℝ) - 1 < (4 : ℝ) ^ (k - 1) := by
    have hnat : (2 * k - 1 : ℕ) < 4 ^ (k - 1) := hlt
    have hcast : ((2 * k - 1 : ℕ) : ℝ) < ((4 ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    have hsub : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
      have : 1 ≤ 2 * k := by omega
      push_cast [this]
      ring
    rw [hsub] at hcast
    simpa using hcast
  have hpow : (0 : ℝ) < (4 : ℝ) ^ (k - 1) := by positivity
  have hfac :
      (1 : ℝ) / 4 ^ (k - 1) - (2 * (k : ℝ) - 1) * ((1 : ℝ) / 4 ^ (k - 1)) ^ 2 =
        ((4 : ℝ) ^ (k - 1) - (2 * (k : ℝ) - 1)) / ((4 : ℝ) ^ (k - 1)) ^ 2 := by
    field_simp [ne_of_gt hpow]
  rw [hfac]
  exact div_pos (sub_pos.mpr hltR) (sq_pos_of_pos hpow)

private theorem shapeVariance_bridge (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) :
    shapeVariance N S =
      (subtreeVariance N k - expectedSubtreeDensity N k) / (catalan (k - 1) : ℝ) ^ 2 +
        expectedShapeDensity N S := by
  have hc_pos : (0 : ℝ) < (catalan (k - 1) : ℝ) := by
    exact_mod_cast catalan_pos_of_nat (k - 1)
  have hc_ne : (catalan (k - 1) : ℝ) ≠ 0 := ne_of_gt hc_pos
  dsimp [shapeVariance, subtreeVariance]
  rw [shapeSecondMoment_eq_pair_add_avg N hk hkN S]
  rw [subtreeSecondMoment_eq_pair_add_avg N k hk hkN]
  rw [globalSubtreePairMultiplicity_eq_mul_shape N hk hkN S]
  rw [expectedSubtreeDensity_eq_mul_shape N hk hkN S]
  push_cast
  field_simp [hc_ne]
  ring

/-- **Linear Single-Shape Variance Scaling (Constant Limit):**
For fixed `k ≥ 2` and `S : FullBracketing k`, letting `q_k = 1 / 4^{k-1}`,
`Var(n_S)(N) - (q_k - (2k - 1) * q_k^2) * N` converges to a finite constant as `N → ∞`. -/
theorem shapeVariance_sub_linear_tendsto {k : ℕ} (hk : 2 ≤ k) (S : FullBracketing k) :
    ∃ C : ℝ, Tendsto
      (fun N : ℕ =>
        shapeVariance N S -
          ((1 : ℝ) / 4 ^ (k - 1) -
            (2 * (k : ℝ) - 1) * ((1 : ℝ) / 4 ^ (k - 1)) ^ 2) * (N : ℝ))
      atTop (𝓝 C) := by
  have hc_pos : (0 : ℝ) < (catalan (k - 1) : ℝ) := by
    exact_mod_cast catalan_pos_of_nat (k - 1)
  have hc_ne : (catalan (k - 1) : ℝ) ≠ 0 := ne_of_gt hc_pos
  obtain ⟨C_var, hvar⟩ := subtreeVariance_sub_linear_tendsto k hk
  have hE := expectedSubtreeDensity_sub_linear_tendsto k hk
  have hS := expectedShapeDensity_sub_linear_tendsto hk S
  have hcomb :=
    ((hvar.sub hE).div_const ((catalan (k - 1) : ℝ) ^ 2)).add hS
  refine ⟨_, hcomb.congr' ?_⟩
  filter_upwards [eventually_ge_atTop k] with N hN
  rw [shapeVariance_bridge N hk hN S]
  field_simp [hc_ne]
  ring

/-- **Linear Single-Shape Variance Scaling (Ratio Limit):**
For fixed `k ≥ 2` and `S : FullBracketing k`,
`Var(n_S)(N) / N → 1 / 4^(k-1) - (2k - 1) * (1 / 4^(k-1))^2` as `N → ∞`. -/
theorem shapeVariance_div_tendsto {k : ℕ} (hk : 2 ≤ k) (S : FullBracketing k) :
    Tendsto (fun N : ℕ => shapeVariance N S / (N : ℝ)) atTop
      (𝓝 ((1 : ℝ) / 4 ^ (k - 1) -
        (2 * (k : ℝ) - 1) * ((1 : ℝ) / 4 ^ (k - 1)) ^ 2)) := by
  obtain ⟨C, hC⟩ := shapeVariance_sub_linear_tendsto hk S
  set s := (1 : ℝ) / 4 ^ (k - 1) - (2 * (k : ℝ) - 1) * ((1 : ℝ) / 4 ^ (k - 1)) ^ 2
  have hdiv : Tendsto (fun N : ℕ => (shapeVariance N S - s * (N : ℝ)) / (N : ℝ))
      atTop (𝓝 0) :=
    hC.div_atTop tendsto_natCast_atTop_atTop
  have hadd := hdiv.add (tendsto_const_nhds (x := s))
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  field_simp [hN0]
  ring

/-- **Linear Single-Shape Variance Big-O Bound:** `Var(n_S)(N) = O(N)` as `N → ∞`. -/
theorem shapeVariance_asymptotic {k : ℕ} (hk : 2 ≤ k) (S : FullBracketing k) :
    (fun N : ℕ => shapeVariance N S) =O[atTop] (fun N : ℕ => (N : ℝ)) := by
  have hdiv := (shapeVariance_div_tendsto hk S).isBigO_one ℝ
  rw [Asymptotics.isBigO_iff] at hdiv ⊢
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c, ?_⟩
  filter_upwards [hc, eventually_ge_atTop 1] with N hNc hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  rw [norm_div, Real.norm_of_nonneg hNpos.le, norm_one] at hNc
  calc
    ‖shapeVariance N S‖ = (‖shapeVariance N S‖ / (N : ℝ)) * (N : ℝ) := by
      field_simp [ne_of_gt hNpos]
    _ ≤ (c * 1) * (N : ℝ) := by gcongr
    _ = c * ‖(N : ℝ)‖ := by rw [Real.norm_of_nonneg hNpos.le]; ring

/-- **Finite-N Chebyshev Concentration Bound (Single Shape):**
For `k ≥ 2`, `k ≤ N`, `S : FullBracketing k`, and `ε > 0`, the uniform probability that
`n_S(T) / N` deviates from `1 / 4^(k-1)` by at least `ε` is bounded by
`(Var(n_S)(N) + (E[n_S](N) - (1 / 4^(k-1)) * N)^2) / (ε^2 * N^2)`. -/
theorem shapeDensity_concentration_bound (N : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N)
    (S : FullBracketing k) (ε : ℝ) (hε : 0 < ε) :
    (MeasureTheory.Measure.uniformOfFinset
        (Finset.univ : Finset (FullBracketing N))).real
      { T : FullBracketing N |
        ε ≤ |(shapeCount T S : ℝ) / (N : ℝ) - (1 : ℝ) / 4 ^ (k - 1)| } ≤
      (shapeVariance N S +
        (expectedShapeDensity N S - ((1 : ℝ) / 4 ^ (k - 1)) * (N : ℝ)) ^ 2) /
        (ε ^ 2 * (N : ℝ) ^ 2) := by
  have hN : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have _ : Nonempty (FullBracketing N) := fullBracketing_nonempty_of_pos N hN
  have hcard_pos : (0 : ℝ) < (Fintype.card (FullBracketing N) : ℝ) := by positivity
  have hcard_ne : (Fintype.card (FullBracketing N) : ℝ) ≠ 0 := ne_of_gt hcard_pos
  set q : ℝ := (1 : ℝ) / 4 ^ (k - 1)
  set μ : ℝ := expectedShapeDensity N S
  let c : FullBracketing N → ℝ := fun T => (shapeCount T S : ℝ)
  let A : Finset (FullBracketing N) :=
    Finset.univ.filter (fun T => ε ≤ |c T / (N : ℝ) - q|)
  have hmeas :
      (MeasureTheory.Measure.uniformOfFinset
          (Finset.univ : Finset (FullBracketing N))).real
        { T : FullBracketing N | ε ≤ |c T / (N : ℝ) - q| } =
        (A.card : ℝ) / (Fintype.card (FullBracketing N) : ℝ) := by
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.uniformOfFinset_apply]
    simp only [Finset.card_univ, ENNReal.toReal_div, ENNReal.toReal_natCast]
    congr 2
  have hterm : ∀ T ∈ A, ε ^ 2 * (N : ℝ) ^ 2 ≤ (c T - q * (N : ℝ)) ^ 2 := by
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, A] at hT
    have hdiff : |c T / (N : ℝ) - q| = |c T - q * (N : ℝ)| / (N : ℝ) := by
      have hdiv : c T / (N : ℝ) - q = (c T - q * (N : ℝ)) / (N : ℝ) := by
        field_simp [hN0]
      rw [hdiv, abs_div, abs_of_pos hNpos]
    rw [hdiff, le_div_iff₀ hNpos] at hT
    have hsq : (ε * (N : ℝ)) ^ 2 ≤ |c T - q * (N : ℝ)| ^ 2 := by gcongr
    rw [sq_abs] at hsq
    linarith
  have hsumA : (A.card : ℝ) * (ε ^ 2 * (N : ℝ) ^ 2) ≤
      ∑ T : FullBracketing N, (c T - q * (N : ℝ)) ^ 2 := by
    calc
      (A.card : ℝ) * (ε ^ 2 * (N : ℝ) ^ 2)
        = ∑ _T ∈ A, ε ^ 2 * (N : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ T ∈ A, (c T - q * (N : ℝ)) ^ 2 := Finset.sum_le_sum hterm
      _ ≤ ∑ T : FullBracketing N, (c T - q * (N : ℝ)) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg (fun T => sq_nonneg _)
  have hsum_id :
      (∑ T : FullBracketing N, (c T - q * (N : ℝ)) ^ 2) =
        (∑ T : FullBracketing N, (c T - μ) ^ 2) +
          (Fintype.card (FullBracketing N) : ℝ) * (μ - q * (N : ℝ)) ^ 2 := by
    have havg : (∑ T : FullBracketing N, c T) = (Fintype.card (FullBracketing N) : ℝ) * μ := by
      have h := expectedShapeDensity_eq_tree_avg N hk hkN S
      change μ = (∑ T : FullBracketing N, c T) / (Fintype.card (FullBracketing N) : ℝ) at h
      rw [h]
      field_simp [hcard_ne]
    have hsplit : ∀ T : FullBracketing N,
        (c T - q * (N : ℝ)) ^ 2 =
          (c T - μ) ^ 2 + 2 * (μ - q * (N : ℝ)) * (c T - μ) + (μ - q * (N : ℝ)) ^ 2 := by
      intro T; ring
    have hmid : (∑ T : FullBracketing N, 2 * (μ - q * (N : ℝ)) * (c T - μ)) = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, havg]
      ring
    simp_rw [hsplit, Finset.sum_add_distrib, hmid, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hvar : (∑ T : FullBracketing N, (c T - μ) ^ 2) =
      (Fintype.card (FullBracketing N) : ℝ) * shapeVariance N S := by
    have hv := shapeVariance_eq_sum_sq_sub N hk hkN S
    change shapeVariance N S =
      (∑ T : FullBracketing N, (c T - μ) ^ 2) / (Fintype.card (FullBracketing N) : ℝ) at hv
    rw [hv]
    field_simp [hcard_ne]
  rw [hmeas]
  have hden_pos : 0 < ε ^ 2 * (N : ℝ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hcard_pos hden_pos]
  calc
    (A.card : ℝ) * (ε ^ 2 * (N : ℝ) ^ 2)
      ≤ ∑ T : FullBracketing N, (c T - q * (N : ℝ)) ^ 2 := hsumA
    _ = (shapeVariance N S + (μ - q * (N : ℝ)) ^ 2) *
          (Fintype.card (FullBracketing N) : ℝ) := by
        rw [hsum_id, hvar]; ring

/-- **Aldous Fringe Law Concentration (Single-Shape):**
For every fixed `k ≥ 2`, every pattern `S : FullBracketing k`, and every `ε > 0`,
`ℙ(|n_S(T) / N - 1 / 4^(k-1)| ≥ ε) → 0` as `N → ∞`. -/
theorem shapeDensity_concentration_tendsto {k : ℕ} (hk : 2 ≤ k) (S : FullBracketing k)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun N : ℕ =>
        (MeasureTheory.Measure.uniformOfFinset
            (Finset.univ : Finset (FullBracketing N))).real
          { T : FullBracketing N |
            ε ≤ |(shapeCount T S : ℝ) / (N : ℝ) - (1 : ℝ) / 4 ^ (k - 1)| })
      atTop (𝓝 0) := by
  set q : ℝ := (1 : ℝ) / 4 ^ (k - 1)
  have hvar : Tendsto (fun N : ℕ => shapeVariance N S / (ε ^ 2 * (N : ℝ) ^ 2)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ => (1 / ε ^ 2) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hs := (shapeVariance_div_tendsto hk S).mul hinv
    rw [mul_zero] at hs
    refine hs.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hε0 : ε ≠ 0 := ne_of_gt hε
    field_simp [hN0, hε0]
  have hmean : Tendsto
      (fun N : ℕ =>
        (expectedShapeDensity N S - q * (N : ℝ)) ^ 2 / (ε ^ 2 * (N : ℝ) ^ 2))
      atTop (𝓝 0) := by
    have hE := (expectedShapeDensity_sub_linear_tendsto hk S).pow 2
    have hdiv : Tendsto (fun N : ℕ =>
        (expectedShapeDensity N S - q * (N : ℝ)) ^ 2 / ((N : ℝ) ^ 2)) atTop (𝓝 0) := by
      have hsq : Tendsto (fun N : ℕ => (N : ℝ) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
      exact hE.div_atTop hsq
    have hmul := hdiv.mul (tendsto_const_nhds (x := 1 / ε ^ 2))
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hε0 : ε ≠ 0 := ne_of_gt hε
    field_simp [hN0, hε0]
  have htop := hvar.add hmean
  rw [zero_add] at htop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop ?_ ?_
  · filter_upwards with N
    exact ENNReal.toReal_nonneg
  · filter_upwards [eventually_ge_atTop k] with N hN
    have hb := shapeDensity_concentration_bound N hk hN S ε hε
    simpa only [add_div] using hb

/-- **Single-Shape Universality:**
Every fixed finite binary tree shape `S : FullBracketing k` (`2 ≤ k`) appears at least once in
a uniform random `N`-leaf binary tree with probability tending to `1` as `N → ∞`. -/
theorem shape_universality_tendsto {k : ℕ} (hk : 2 ≤ k) (S : FullBracketing k) :
    Tendsto
      (fun N : ℕ =>
        (MeasureTheory.Measure.uniformOfFinset
            (Finset.univ : Finset (FullBracketing N))).real
          { T : FullBracketing N | 1 ≤ shapeCount T S })
      atTop (𝓝 1) := by
  set q : ℝ := (1 : ℝ) / 4 ^ (k - 1)
  have hq : 0 < q := by positivity
  have hconc := shapeDensity_concentration_tendsto hk S q hq
  have hzero :
      Tendsto
        (fun N : ℕ =>
          (MeasureTheory.Measure.uniformOfFinset
              (Finset.univ : Finset (FullBracketing N))).real
            { T : FullBracketing N | shapeCount T S = 0 })
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconc ?_ ?_
    · filter_upwards with N
      exact ENNReal.toReal_nonneg
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have _ : Nonempty (FullBracketing N) := fullBracketing_nonempty_of_pos N hN
      simp only [MeasureTheory.Measure.real_def, MeasureTheory.Measure.uniformOfFinset_apply,
        Finset.card_univ, ENNReal.toReal_div, ENNReal.toReal_natCast]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      norm_cast
      refine Finset.card_le_card fun T hT => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hT ⊢
      rw [hT, Nat.cast_zero, zero_div, zero_sub, abs_neg, abs_of_pos (by positivity)]
      dsimp [q]
      push_cast
      rfl
  have hcomp :
      Tendsto
        (fun N : ℕ =>
          1 - (MeasureTheory.Measure.uniformOfFinset
              (Finset.univ : Finset (FullBracketing N))).real
            { T : FullBracketing N | shapeCount T S = 0 })
        atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hzero
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have _ : Nonempty (FullBracketing N) := fullBracketing_nonempty_of_pos N hN
  have hcard_pos : (0 : ℝ) < (Fintype.card (FullBracketing N) : ℝ) := by positivity
  have hcard_ne : (Fintype.card (FullBracketing N) : ℝ) ≠ 0 := ne_of_gt hcard_pos
  simp only [MeasureTheory.Measure.real_def, MeasureTheory.Measure.uniformOfFinset_apply,
    Finset.card_univ, ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hsplit :
      (Finset.univ.filter (· ∈ { T : FullBracketing N | shapeCount T S = 0 })).card +
        (Finset.univ.filter (· ∈ { T : FullBracketing N | 1 ≤ shapeCount T S })).card =
        Fintype.card (FullBracketing N) := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have h1 : ∀ T : FullBracketing N,
        (if T ∈ { T : FullBracketing N | shapeCount T S = 0 } then 1 else 0) +
          (if T ∈ { T : FullBracketing N | 1 ≤ shapeCount T S } then 1 else 0) = 1 := by
      intro T
      simp only [Set.mem_ofPred_eq]
      split_ifs <;> omega
    simp_rw [h1, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  have hsumR :
      ((Finset.univ.filter (· ∈ { T : FullBracketing N | shapeCount T S = 0 })).card : ℝ) +
        ((Finset.univ.filter
          (· ∈ { T : FullBracketing N | 1 ≤ shapeCount T S })).card : ℝ) =
        (Fintype.card (FullBracketing N) : ℝ) := by
    exact_mod_cast hsplit
  field_simp [hcard_ne]
  rw [sub_eq_iff_eq_add, add_comm]
  symm
  convert hsumR

private theorem catalan_succ_recurrence (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 : (n + 2) * catalan (n + 1) = (n + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 : (n + 1) * (n + 1).centralBinom = 2 * (2 * n + 1) * n.centralBinom :=
    Nat.succ_mul_centralBinom_succ n
  have h3 : (n + 1) * catalan n = n.centralBinom :=
    succ_mul_catalan_eq_centralBinom n
  have h4 : (n + 1) * ((n + 2) * catalan (n + 1)) =
      (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    rw [h1, h2, ← h3]
    ring
  exact Nat.mul_left_cancel (Nat.succ_pos n) h4

private noncomputable def fringeTail (n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 1) * (catalan n : ℝ) / 4 ^ n

private theorem fringeTail_zero : fringeTail 0 = 1 := by
  simp [fringeTail, catalan_zero]

private theorem fringeTail_nonneg (n : ℕ) : 0 ≤ fringeTail n := by
  dsimp [fringeTail]
  positivity

private theorem fringeTail_sub_succ (n : ℕ) :
    fringeTail n - fringeTail (n + 1) = (catalan (n + 1) : ℝ) / 4 ^ (n + 1) := by
  have hrec : ((n : ℝ) + 2) * (catalan (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (catalan n : ℝ) := by
    have hnat := catalan_succ_recurrence n
    exact_mod_cast hnat
  dsimp [fringeTail]
  have hpow : (4 : ℝ) ^ (n + 1) = 4 * (4 : ℝ) ^ n := pow_succ' 4 n
  have hcat : (2 * (n : ℝ) + 1) * (catalan n : ℝ) =
      ((n : ℝ) + 2) / 2 * (catalan (n + 1) : ℝ) := by
    linarith
  rw [hcat, hpow]
  push_cast
  ring

private noncomputable def centralBinomScaled (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / 4 ^ n

private theorem centralBinomScaled_sq_bound (n : ℕ) :
    (2 * (n : ℝ) + 1) * centralBinomScaled n ^ 2 ≤ 1 := by
  induction n with
  | zero =>
    norm_num [centralBinomScaled, Nat.centralBinom_zero]
  | succ n ih =>
    have hrec : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
        2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
      have hnat := Nat.succ_mul_centralBinom_succ n
      exact_mod_cast hnat
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hstep : centralBinomScaled (n + 1) =
        ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) * centralBinomScaled n := by
      dsimp [centralBinomScaled]
      have hpow : (4 : ℝ) ^ (n + 1) = 4 * (4 : ℝ) ^ n := pow_succ' 4 n
      have hpow0 : (4 : ℝ) ^ n ≠ 0 := by positivity
      rw [hpow]
      field_simp [hn1, hpow0]
      nlinarith
    have hnonneg : 0 ≤ (2 * (n : ℝ) + 1) * centralBinomScaled n ^ 2 := by
      have h1 : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := by positivity
      exact mul_nonneg h1 (sq_nonneg _)
    have hratio :
        (2 * ((n + 1 : ℕ) : ℝ) + 1) * ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) ^ 2 ≤
          2 * (n : ℝ) + 1 := by
      have hden : (0 : ℝ) < (2 * ((n : ℝ) + 1)) ^ 2 := by positivity
      push_cast
      rw [div_pow, mul_div_assoc', div_le_iff₀ hden]
      nlinarith
    have hmul :
        (2 * ((n + 1 : ℕ) : ℝ) + 1) * centralBinomScaled (n + 1) ^ 2 =
          ((2 * ((n + 1 : ℕ) : ℝ) + 1) * ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) ^ 2) *
            centralBinomScaled n ^ 2 := by
      rw [hstep, mul_pow]
      ring
    rw [hmul]
    calc
      ((2 * ((n + 1 : ℕ) : ℝ) + 1) * ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) ^ 2) *
          centralBinomScaled n ^ 2
        ≤ (2 * (n : ℝ) + 1) * centralBinomScaled n ^ 2 :=
            mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
      _ ≤ 1 := ih

private theorem tendsto_fringeTail : Tendsto fringeTail atTop (𝓝 0) := by
  have hle_cb : ∀ n : ℕ, fringeTail n ≤ 2 * centralBinomScaled n := by
    intro n
    have hmul : ((n : ℝ) + 1) * (catalan n : ℝ) = (Nat.centralBinom n : ℝ) := by
      have hnat := succ_mul_catalan_eq_centralBinom n
      exact_mod_cast hnat
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hrel : fringeTail n = ((2 * (n : ℝ) + 1) / ((n : ℝ) + 1)) * centralBinomScaled n := by
      dsimp [fringeTail, centralBinomScaled]
      have hpow0 : (4 : ℝ) ^ n ≠ 0 := by positivity
      field_simp [ne_of_gt hn1, hpow0]
      nlinarith
    have hcoeff : (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ hn1]
      linarith
    have hcb_nonneg : 0 ≤ centralBinomScaled n := by
      dsimp [centralBinomScaled]
      positivity
    rw [hrel]
    exact mul_le_mul_of_nonneg_right hcoeff hcb_nonneg
  have hsq_bound : ∀ n : ℕ, fringeTail n ^ 2 ≤ 4 / (2 * (n : ℝ) + 1) := by
    intro n
    have h1 : fringeTail n ^ 2 ≤ (2 * centralBinomScaled n) ^ 2 := by
      gcongr
      · exact fringeTail_nonneg n
      · exact hle_cb n
    have h2 : centralBinomScaled n ^ 2 ≤ 1 / (2 * (n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      rw [le_div_iff₀ hpos, mul_comm]
      exact centralBinomScaled_sq_bound n
    calc
      fringeTail n ^ 2 ≤ 4 * centralBinomScaled n ^ 2 := by linarith
      _ ≤ 4 * (1 / (2 * (n : ℝ) + 1)) := by linarith
      _ = 4 / (2 * (n : ℝ) + 1) := by ring
  have hden_top : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
    ((tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_add
      tendsto_const_nhds)
  have hlim_bd : Tendsto (fun n : ℕ => (4 : ℝ) / (2 * (n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden_top
  have hsq_lim : Tendsto (fun n : ℕ => fringeTail n ^ 2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim_bd
      (fun n => sq_nonneg (fringeTail n)) hsq_bound
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (fringeTail n ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hsq_lim
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  exact Real.sqrt_sq (fringeTail_nonneg n)

/-- **Fringe Mass Normalization:**
The total asymptotic fringe probability mass sums to `1`:
`∑ k ∈ Finset.Ico 2 M, C_{k-1} / 4^(k-1) → 1` as `M → ∞`. -/
theorem fringeMass_partialSum_tendsto :
    Tendsto
      (fun M : ℕ => ∑ k ∈ Finset.Ico 2 M, (catalan (k - 1) : ℝ) / 4 ^ (k - 1))
      atTop (𝓝 1) := by
  have hsub_top : Tendsto (fun M : ℕ => M - 2) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b + 2, fun M hM => by omega⟩
  have htail_lim : Tendsto (fun M : ℕ => 1 - fringeTail (M - 2)) atTop (𝓝 1) := by
    have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_fringeTail.comp hsub_top)
    simpa only [Function.comp_def, sub_zero] using hsub
  refine htail_lim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  rw [Finset.sum_Ico_eq_sum_range]
  have hshift :
      (∑ x ∈ Finset.range (M - 2), (catalan (2 + x - 1) : ℝ) / 4 ^ (2 + x - 1)) =
        ∑ x ∈ Finset.range (M - 2), (fringeTail x - fringeTail (x + 1)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : 2 + x - 1 = x + 1 := by omega
    rw [hx, fringeTail_sub_succ]
  rw [hshift, Finset.sum_range_sub' fringeTail (M - 2), fringeTail_zero]

end FringeVarianceAndConcentration

end FunctorialGeometry
