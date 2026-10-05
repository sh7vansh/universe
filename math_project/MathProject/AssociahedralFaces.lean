/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralRealization
import Mathlib.LinearAlgebra.Pi

/-! # Supporting-function certificates for Loday's convex hull -/

namespace FunctorialGeometry

open Finset

def gapCost (c w : ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ i ∈ Ico a (b - 1), c i * w i

theorem gapCost_shift (c w : ℕ → ℝ) (a b : ℕ) (r : ℝ) :
    gapCost c w a b = r * gapSum w a b + gapCost (fun i => c i - r) w a b := by
  unfold gapCost gapSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem gapCost_cross (c w : ℕ → ℝ) (a cut b : ℕ) (ha : a < cut) (hb : cut < b) :
    gapCost c w a b = gapCost c w a cut + c (cut - 1) * w (cut - 1) + gapCost c w cut b :=
  gapSum_cross (fun i => c i * w i) a cut b ha hb

/-- A linear functional is a sum of interval functionals on one binary tree.
All proper-interval coefficients are nonnegative; only the whole-word coefficient
can have either sign. This is a certificate for every supporting face. -/
theorem tree_normal_certificate (length : ℕ) (hpos : 0 < length)
    (start : ℕ) (c : ℕ → ℝ) :
    ∃ (t : BinaryTree Unit) (terms : List (BracketSpan × ℝ)),
      t.numLeaves = length ∧
      (∀ z ∈ terms, z.1 ∈ treeSpans t start) ∧
      (∀ z ∈ terms, z.1 ≠ (start, start + length) → 0 ≤ z.2) ∧
      ((∀ i ∈ Ico start (start + length - 1), 0 ≤ c i) → ∀ z ∈ terms, 0 ≤ z.2) ∧
      ∀ w : ℕ → ℝ, gapCost c w start (start + length) =
        (terms.map (fun z => z.2 * gapSum w z.1.1 z.1.2)).sum := by
  induction length using Nat.strong_induction_on generalizing start c with
  | h length ih =>
    by_cases h1 : length = 1
    · refine ⟨.nil, [], h1.symm, by simp, by simp, by simp, ?_⟩
      intro w; simp [gapCost, h1]
    have hn : (Ico start (start + length - 1)).Nonempty := by
      exact ⟨start, Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩⟩
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Ico start (start + length - 1)) c hn
    have hj' := Finset.mem_Ico.mp hj
    let cut := j + 1
    let c' := fun i => c i - c j
    have hc' : ∀ i ∈ Ico start (start + length - 1), 0 ≤ c' i := by
      intro i hi; exact sub_nonneg.mpr (hmin i hi)
    obtain ⟨l, tl, hl, htl, hpl, hnpl, hcl⟩ :=
      ih (cut - start) (by dsimp [cut]; omega) (by dsimp [cut]; omega) start c'
    obtain ⟨r, tr, hr, htr, hpr, hnpr, hcr⟩ :=
      ih (start + length - cut) (by dsimp [cut]; omega) (by dsimp [cut]; omega) cut c'
    have hel : start + (cut - start) = cut := by dsimp [cut]; omega
    have her : cut + (start + length - cut) = start + length := by dsimp [cut]; omega
    have hleftpos : ∀ z ∈ tl, 0 ≤ z.2 := hnpl (by
      intro i hi; apply hc' i
      have hi := Finset.mem_Ico.mp hi
      apply Finset.mem_Ico.mpr
      dsimp [cut] at *; omega)
    have hrightpos : ∀ z ∈ tr, 0 ≤ z.2 := hnpr (by
      intro i hi; apply hc' i
      have hi := Finset.mem_Ico.mp hi
      apply Finset.mem_Ico.mpr
      dsimp [cut] at *; omega)
    let root : BracketSpan := (start, start + length)
    let terms := (root, c j) :: (tl ++ tr)
    have ht : (.node () l r : BinaryTree Unit).numLeaves = length := by
      simp only [BinaryTree.numLeaves, hl, hr]
      dsimp [cut]; omega
    refine ⟨.node () l r, terms, ht, ?_, ?_, ?_, ?_⟩
    · intro z hz
      simp only [terms, List.mem_cons, List.mem_append] at hz
      rcases hz with rfl | hz | hz
      · have he : root = (start, start + l.numLeaves + r.numLeaves) := by
          dsimp [root]; rw [hl, hr]; congr 1; dsimp [cut]; omega
        exact he ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (htl z hz))
      · have he : start + l.numLeaves = cut := by rw [hl]; exact hel
        rw [← he] at htr
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (htr z hz))
    · intro z hz hproper
      simp only [terms, List.mem_cons, List.mem_append] at hz
      rcases hz with rfl | hz | hz
      · exact False.elim (hproper rfl)
      · exact hleftpos z hz
      · exact hrightpos z hz
    · intro hc z hz
      simp only [terms, List.mem_cons, List.mem_append] at hz
      rcases hz with rfl | hz | hz
      · exact hc j hj
      · exact hleftpos z hz
      · exact hrightpos z hz
    · intro w
      have hcl' := hcl w
      have hcr' := hcr w
      rw [hel] at hcl'
      rw [her] at hcr'
      rw [gapCost_shift c w start (start + length) (c j)]
      change c j * gapSum w start (start + length) + gapCost c' w start (start + length) = _
      rw [gapCost_cross c' w start cut (start + length) (by dsimp [cut]; omega)
        (by dsimp [cut]; omega), hcl', hcr']
      have hjzero : c' (cut - 1) = 0 := by dsimp [c', cut]; simp
      simp only [terms, List.map_cons, List.map_append, List.sum_cons, List.sum_append,
        hjzero, zero_mul, add_zero, root]

theorem lodayPoint_tight_iff (n : ℕ) (t : FullBracketing (n + 2))
    (b : ProperBracket (n + 2)) :
    intervalLinear n b.left.val b.right.val (lodayPoint n t) =
      Nat.choose (b.right.val - b.left.val) 2 ↔ bracketSpan b ∈ treeSpans t.val 0 := by
  have hv := (properBracketSpans_valid ({b} : Finset (ProperBracket (n + 2)))
    (bracketSpan b) (Finset.mem_image.mpr ⟨b, Finset.mem_singleton_self _, rfl⟩)).1
  have hb : b.right.val ≤ n + 2 := by have h := b.right.isLt; omega
  rw [lodayPoint_interval n t b.left.val b.right.val hb]
  have hv' : SpanValid 0 t.val.numLeaves (bracketSpan b) := by simpa only [t.property] using hv
  exact (Nat.cast_inj (R := ℝ)).trans (treeIntervalSum_eq_iff t.val 0 (bracketSpan b) hv')

def LodayBracketFace (n : ℕ) (p : PartialBracketing (n + 2)) : Set (LodaySpace n) :=
  {x | x ∈ LodayPolytope n ∧ ∀ b ∈ p.val,
    intervalLinear n b.left.val b.right.val x = Nat.choose (b.right.val - b.left.val) 2}

theorem LodayBracketFace_nonempty (n : ℕ) (p : PartialBracketing (n + 2)) :
    (LodayBracketFace n p).Nonempty := by
  have hs := spanFamily_insert_root (by omega : 2 ≤ n + 2) (properBracketSpans_family p)
  obtain ⟨t, ht, hsub⟩ := spanFamily_complete (n + 2) (by omega) 0 _ hs
  let t' : FullBracketing (n + 2) := ⟨t, ht⟩
  refine ⟨lodayPoint n t', subset_convexHull ℝ _ (Set.mem_range_self t'), ?_⟩
  intro b hb
  apply (lodayPoint_tight_iff n t' b).mpr
  exact hsub (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb, rfl⟩))

/-- The convex face order is exactly the bracket order. -/
theorem LodayBracketFace_order_iff (n : ℕ) (p q : PartialBracketing (n + 2)) :
    LodayBracketFace n p ⊆ LodayBracketFace n q ↔ p ≤ q := by
  constructor
  · intro h
    change q.val ⊆ p.val
    intro b hb
    by_contra hnot
    obtain ⟨t, hsub, havoid⟩ := partialBracketing_completion_avoiding (by omega) p b hnot
    have ht : lodayPoint n t ∈ LodayBracketFace n p := by
      constructor
      · exact subset_convexHull ℝ _ (Set.mem_range_self t)
      · intro c hc
        apply (lodayPoint_tight_iff n t c).mpr
        exact hsub (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
    exact havoid ((lodayPoint_tight_iff n t b).mp ((h ht).2 b hb))
  · intro h x hx
    exact ⟨hx.1, fun b hb => hx.2 b (h hb)⟩

def bracketFaceLinear (n : ℕ) (p : PartialBracketing (n + 2)) : LodaySpace n →ₗ[ℝ] ℝ :=
  ∑ b ∈ p.val, intervalLinear n b.left.val b.right.val

def bracketFaceLower (n : ℕ) (p : PartialBracketing (n + 2)) : ℝ :=
  ∑ b ∈ p.val, (Nat.choose (b.right.val - b.left.val) 2 : ℝ)

theorem bracketFaceLinear_lower (n : ℕ) (p : PartialBracketing (n + 2))
    {x : LodaySpace n} (hx : x ∈ LodayPolytope n) :
    bracketFaceLower n p ≤ bracketFaceLinear n p x := by
  simp only [bracketFaceLinear, LinearMap.sum_apply, bracketFaceLower]
  apply Finset.sum_le_sum
  intro b _
  have hg := b.length_two
  have hb := b.right.isLt
  exact LodayPolytope_interval n hx _ _ (by omega) (by omega)

theorem bracketFaceLinear_eq_iff (n : ℕ) (p : PartialBracketing (n + 2))
    {x : LodaySpace n} (hx : x ∈ LodayPolytope n) :
    bracketFaceLinear n p x = bracketFaceLower n p ↔ x ∈ LodayBracketFace n p := by
  have hnonneg : ∀ b ∈ p.val,
      0 ≤ intervalLinear n b.left.val b.right.val x - Nat.choose (b.right.val - b.left.val) 2 := by
    intro b _
    have hg := b.length_two
    have hb := b.right.isLt
    exact sub_nonneg.mpr (LodayPolytope_interval n hx _ _ (by omega) (by omega))
  have he : bracketFaceLinear n p x - bracketFaceLower n p =
      ∑ b ∈ p.val, (intervalLinear n b.left.val b.right.val x -
        Nat.choose (b.right.val - b.left.val) 2) := by
    simp [bracketFaceLinear, bracketFaceLower, Finset.sum_sub_distrib]
  constructor
  · intro h
    have hz : (∑ b ∈ p.val, (intervalLinear n b.left.val b.right.val x -
        Nat.choose (b.right.val - b.left.val) 2)) = 0 := by rw [← he, h, sub_self]
    exact ⟨hx, fun b hb => sub_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz b hb)⟩
  · intro h
    simp only [bracketFaceLinear, LinearMap.sum_apply, bracketFaceLower]
    exact Finset.sum_congr rfl (fun b hb => h.2 b hb)

/-- A nonempty geometric face defined by a supporting linear functional. -/
abbrev LodayExposedFace (n : ℕ) :=
  {F : Set (LodaySpace n) // F.Nonempty ∧ ∃ f : LodaySpace n →ₗ[ℝ] ℝ,
    ∀ x, x ∈ F ↔ x ∈ LodayPolytope n ∧ ∀ y ∈ LodayPolytope n, f x ≤ f y}

/-- Every bracket face is an actual supporting face of the explicit convex hull. -/
def bracketExposedFace (n : ℕ) (p : PartialBracketing (n + 2)) : LodayExposedFace n :=
  ⟨LodayBracketFace n p, LodayBracketFace_nonempty n p, bracketFaceLinear n p, by
    intro x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      rw [(bracketFaceLinear_eq_iff n p hx.1).mpr hx]
      exact fun y hy => bracketFaceLinear_lower n p hy
    · rintro ⟨hx, hmin⟩
      obtain ⟨y, hy⟩ := LodayBracketFace_nonempty n p
      have hle := hmin y hy.1
      rw [(bracketFaceLinear_eq_iff n p hy.1).mpr hy] at hle
      exact (bracketFaceLinear_eq_iff n p hx).mp
        (le_antisymm hle (bracketFaceLinear_lower n p hx))⟩

def linearCoefficients (n : ℕ) (f : LodaySpace n →ₗ[ℝ] ℝ) : ℕ → ℝ :=
  coordinateAt n (fun i => f (fun j => if i = j then 1 else 0))

theorem linear_eq_gapCost (n : ℕ) (f : LodaySpace n →ₗ[ℝ] ℝ) (x : LodaySpace n) :
    f x = gapCost (linearCoefficients n f) (coordinateAt n x) 0 (n + 2) := by
  rw [LinearMap.pi_apply_eq_sum_univ]
  unfold gapCost
  simp only [Nat.Ico_zero_eq_range]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [linearCoefficients, coordinateAt, dif_pos i.isLt, smul_eq_mul]
  ring

private theorem list_sum_map_sub {α : Type*} (s : List α) (f g : α → ℝ) :
    (s.map f).sum - (s.map g).sum = (s.map (fun z => f z - g z)).sum := by
  induction s with
  | nil => simp
  | cons a s ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

private theorem list_sum_zero_iff {α : Type*} (s : List α) (f : α → ℝ)
    (h : ∀ z ∈ s, 0 ≤ f z) : (s.map f).sum = 0 ↔ ∀ z ∈ s, f z = 0 := by
  induction s with
  | nil => simp
  | cons a s ih =>
    have ha := h a List.mem_cons_self
    have hs : ∀ z ∈ s, 0 ≤ f z := fun z hz => h z (List.mem_cons_of_mem _ hz)
    have hsum : 0 ≤ (s.map f).sum := List.sum_nonneg (by
      intro x hx; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx; exact hs z hz)
    simp only [List.map_cons, List.sum_cons, List.forall_mem_cons]
    rw [← ih hs]
    constructor
    · intro he; constructor <;> linarith
    · rintro ⟨he, hs'⟩; simp [he, hs']

/-- Every nonempty supporting face is given by a compatible partial bracketing. -/
theorem bracketExposedFace_surjective (n : ℕ) : Function.Surjective (bracketExposedFace n) := by
  classical
  intro F
  obtain ⟨f, hf⟩ := F.property.2
  obtain ⟨t, terms, ht, hspan, hpositive, _, hcost⟩ :=
    tree_normal_certificate (n + 2) (by omega) 0 (linearCoefficients n f)
  let t' : FullBracketing (n + 2) := ⟨t, ht⟩
  let base := fun z : BracketSpan × ℝ => (Nat.choose (z.1.2 - z.1.1) 2 : ℝ)
  have hlinear : ∀ x : LodaySpace n, f x =
      (terms.map (fun z => z.2 * intervalLinear n z.1.1 z.1.2 x)).sum := by
    intro x
    rw [linear_eq_gapCost]
    have hc := hcost (coordinateAt n x)
    simpa only [Nat.zero_add, gapSum_coordinateAt] using hc
  have htight : ∀ z ∈ terms, intervalLinear n z.1.1 z.1.2 (lodayPoint n t') = base z := by
    intro z hz
    have hv := treeSpans_valid t 0 z.1 (hspan z hz)
    have hb : z.1.2 ≤ n + 2 := by simpa only [ht, Nat.zero_add] using hv.2.2
    rw [lodayPoint_interval n t' z.1.1 z.1.2 hb]
    exact congrArg (fun k : ℕ => (k : ℝ)) (treeIntervalSum_eq_of_mem t 0 z.1 (hspan z hz))
  let defect := fun (x : LodaySpace n) (z : BracketSpan × ℝ) =>
    z.2 * (intervalLinear n z.1.1 z.1.2 x - base z)
  have hnonneg : ∀ x ∈ LodayPolytope n, ∀ z ∈ terms, 0 ≤ defect x z := by
    intro x hx z hz
    by_cases he : z.1 = (0, n + 2)
    · have hs : intervalLinear n z.1.1 z.1.2 x = base z := by
        dsimp [base]; rw [he]; simp only [Nat.sub_zero]
        exact LodayPolytope_total n hx
      dsimp [defect]; rw [hs, sub_self, mul_zero]
    · have hv := treeSpans_valid t 0 z.1 (hspan z hz)
      have hp := hpositive z hz (by simpa only [Nat.zero_add] using he)
      have hbound := LodayPolytope_interval n hx z.1.1 z.1.2 (by have h := hv.2.1; omega)
        (by simpa only [ht, Nat.zero_add] using hv.2.2)
      exact mul_nonneg hp (sub_nonneg.mpr hbound)
  have hdifference : ∀ x : LodaySpace n,
      f x - f (lodayPoint n t') = (terms.map (defect x)).sum := by
    intro x
    rw [hlinear x, hlinear (lodayPoint n t'), list_sum_map_sub]
    apply congrArg List.sum
    apply List.map_congr_left
    intro z hz
    rw [htight z hz]
    dsimp [defect]; ring
  have hminimum : ∀ x ∈ LodayPolytope n, f (lodayPoint n t') ≤ f x := by
    intro x hx
    have hs : 0 ≤ (terms.map (defect x)).sum := List.sum_nonneg (by
      intro z hz; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz; exact hnonneg x hx q hq)
    rw [← hdifference x] at hs
    exact sub_nonneg.mp hs
  have hzero_iff : ∀ x ∈ LodayPolytope n,
      f x = f (lodayPoint n t') ↔
        ∀ z ∈ terms, z.1 ≠ (0, n + 2) → 0 < z.2 →
          intervalLinear n z.1.1 z.1.2 x = base z := by
    intro x hx
    rw [← sub_eq_zero, hdifference x, list_sum_zero_iff terms (defect x) (hnonneg x hx)]
    constructor
    · intro hz z hmem hproper hp
      have he := hz z hmem
      dsimp [defect] at he
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (ne_of_gt hp))
    · intro hz z hmem
      by_cases he : z.1 = (0, n + 2)
      · have hs : intervalLinear n z.1.1 z.1.2 x = base z := by
          dsimp [base]; rw [he]; simp only [Nat.sub_zero]
          exact LodayPolytope_total n hx
        dsimp [defect]; rw [hs, sub_self, mul_zero]
      · have hp := hpositive z hmem (by simpa only [Nat.zero_add] using he)
        by_cases hp0 : z.2 = 0
        · simp [defect, hp0]
        · have hs := hz z hmem he (lt_of_le_of_ne hp (Ne.symm hp0))
          simp [defect, hs]
  let active := (terms.toFinset.filter (fun z => z.1 ≠ (0, n + 2) ∧ 0 < z.2)).image Prod.fst
  have hactive : ∀ p ∈ active, SpanValid 0 (n + 2) p ∧ p ≠ (0, n + 2) := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    have hz' := Finset.mem_filter.mp hz
    have hv := treeSpans_valid t 0 z.1 (hspan z (List.mem_toFinset.mp hz'.1))
    exact ⟨by simpa only [ht] using hv, hz'.2.1⟩
  let p : PartialBracketing (n + 2) :=
    ⟨spansToBrackets (n + 2) active hactive, by
      intro a ha b hb
      have he := properBracketSpans_spansToBrackets (n + 2) active hactive
      have ha' : bracketSpan a ∈ active := by rw [← he]; exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      have hb' : bracketSpan b ∈ active := by rw [← he]; exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
      obtain ⟨za, hza, hzae⟩ := Finset.mem_image.mp ha'
      obtain ⟨zb, hzb, hzbe⟩ := Finset.mem_image.mp hb'
      have hza' := List.mem_toFinset.mp (Finset.mem_filter.mp hza).1
      have hzb' := List.mem_toFinset.mp (Finset.mem_filter.mp hzb).1
      have hcompat := treeSpans_compatible t 0 _ (hspan za hza') _ (hspan zb hzb')
      rw [hzae, hzbe] at hcompat
      exact hcompat⟩
  have hemap : properBracketSpans p.val = active :=
    properBracketSpans_spansToBrackets (n + 2) active hactive
  have hactive_iff : ∀ x : LodaySpace n,
      (∀ b ∈ p.val, intervalLinear n b.left.val b.right.val x =
        Nat.choose (b.right.val - b.left.val) 2) ↔
      (∀ z ∈ terms, z.1 ≠ (0, n + 2) → 0 < z.2 →
        intervalLinear n z.1.1 z.1.2 x = base z) := by
    intro x
    constructor
    · intro hx z hz hproper hp
      have hzmem : z.1 ∈ active := Finset.mem_image.mpr ⟨z,
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hz, hproper, hp⟩, rfl⟩
      rw [← hemap] at hzmem
      obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hzmem
      have hh := hx b hb
      have he1 := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      dsimp [bracketSpan] at he1 he2
      dsimp [base]; rw [← he1, ← he2]; exact hh
    · intro hx b hb
      have hbmem : bracketSpan b ∈ active := by
        rw [← hemap]; exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
      obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hbmem
      have hz' := Finset.mem_filter.mp hz
      have hh := hx z (List.mem_toFinset.mp hz'.1) hz'.2.1 hz'.2.2
      dsimp [base] at hh
      rw [he] at hh
      exact hh
  refine ⟨p, ?_⟩
  apply Subtype.ext
  ext x
  rw [hf x]
  symm
  constructor
  · rintro ⟨hx, hmin⟩
    have hpt : lodayPoint n t' ∈ LodayPolytope n := subset_convexHull ℝ _ (Set.mem_range_self t')
    have he : f x = f (lodayPoint n t') := le_antisymm (hmin _ hpt) (hminimum x hx)
    exact ⟨hx, (hactive_iff x).mpr ((hzero_iff x hx).mp he)⟩
  · rintro ⟨hx, hp⟩
    have he : f x = f (lodayPoint n t') := (hzero_iff x hx).mpr ((hactive_iff x).mp hp)
    exact ⟨hx, fun y hy => by simpa only [he] using hminimum y hy⟩

/-- The complete nonempty face order of the explicit convex hull. -/
noncomputable def partialBracketing_loday_orderIso (n : ℕ) :
    PartialBracketing (n + 2) ≃o LodayExposedFace n where
  toEquiv := Equiv.ofBijective (bracketExposedFace n) ⟨by
    intro p q he
    have hsets := congrArg Subtype.val he
    apply le_antisymm
    · exact (LodayBracketFace_order_iff n p q).mp hsets.subset
    · exact (LodayBracketFace_order_iff n q p).mp hsets.symm.subset,
    bracketExposedFace_surjective n⟩
  map_rel_iff' := by
    intro p q
    exact LodayBracketFace_order_iff n p q

/-- Polygon faces and geometric supporting faces agree in every dimension. -/
noncomputable def polygon_loday_face_orderIso (n : ℕ) :
    NoncrossingFace (n + 2) ≃o LodayExposedFace n :=
  (partialBracketing_face_orderIso (n + 2)).symm.trans (partialBracketing_loday_orderIso n)

end FunctorialGeometry
