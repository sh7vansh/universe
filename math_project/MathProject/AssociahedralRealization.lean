/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralTrees
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Loday coordinates

At an internal split, the coordinate is the product of the numbers of leaves in
the two children. The indices are the gaps between the ordered leaves.

Reference: J.-L. Loday, *Realization of the Stasheff polytope*,
https://arxiv.org/abs/math/0212126.
-/

namespace FunctorialGeometry

open Finset

/-- Loday's integer gap coordinates, with an arbitrary starting index. -/
def treeGapWeight : BinaryTree Unit → ℕ → ℕ → ℕ
  | .nil, _, _ => 0
  | .node _ l r, start, i =>
    treeGapWeight l start i + treeGapWeight r (start + l.numLeaves) i +
      if i = start + l.numLeaves - 1 then l.numLeaves * r.numLeaves else 0

theorem treeGapWeight_support (t : BinaryTree Unit) (start i : ℕ)
    (h : i < start ∨ start + t.numLeaves - 1 ≤ i) : treeGapWeight t start i = 0 := by
  induction t generalizing start with
  | nil => rfl
  | node _ l r il ir =>
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    simp only [BinaryTree.numLeaves] at h
    have hleft : i < start ∨ start + l.numLeaves - 1 ≤ i := by omega
    have hright : i < start + l.numLeaves ∨
        start + l.numLeaves + r.numLeaves - 1 ≤ i := by omega
    simp only [treeGapWeight, il start hleft, ir (start + l.numLeaves) hright,
      if_neg (by omega : i ≠ start + l.numLeaves - 1)]

/-- The sum on the gaps strictly inside a leaf interval `[a,b)`. -/
def treeIntervalSum (t : BinaryTree Unit) (start a b : ℕ) : ℕ :=
  ∑ i ∈ Ico a (b - 1), treeGapWeight t start i

theorem treeIntervalSum_left (l r : BinaryTree Unit) (start a b : ℕ)
    (hb : b ≤ start + l.numLeaves) :
    treeIntervalSum (.node () l r) start a b = treeIntervalSum l start a b := by
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_Ico.mp hi
  have hl := l.numLeaves_pos
  have hz := treeGapWeight_support r (start + l.numLeaves) i (Or.inl (by omega))
  simp only [treeGapWeight, hz, if_neg (by omega : i ≠ start + l.numLeaves - 1),
    Nat.add_zero]

theorem treeIntervalSum_right (l r : BinaryTree Unit) (start a b : ℕ)
    (ha : start + l.numLeaves ≤ a) :
    treeIntervalSum (.node () l r) start a b =
      treeIntervalSum r (start + l.numLeaves) a b := by
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_Ico.mp hi
  have hl := l.numLeaves_pos
  have hz := treeGapWeight_support l start i (Or.inr (by omega))
  simp only [treeGapWeight, hz, if_neg (by omega : i ≠ start + l.numLeaves - 1),
    Nat.zero_add, Nat.add_zero]

theorem treeGapWeight_root (l r : BinaryTree Unit) (start : ℕ) :
    treeGapWeight (.node () l r) start (start + l.numLeaves - 1) =
      l.numLeaves * r.numLeaves := by
  have hl := l.numLeaves_pos
  have hlz := treeGapWeight_support l start (start + l.numLeaves - 1) (Or.inr (by omega))
  have hrz := treeGapWeight_support r (start + l.numLeaves)
    (start + l.numLeaves - 1) (Or.inl (by omega))
  simp [treeGapWeight, hlz, hrz]

theorem treeIntervalSum_cross (l r : BinaryTree Unit) (start a b : ℕ)
    (ha : a < start + l.numLeaves) (hb : start + l.numLeaves < b) :
    treeIntervalSum (.node () l r) start a b =
      treeIntervalSum l start a (start + l.numLeaves) + l.numLeaves * r.numLeaves +
        treeIntervalSum r (start + l.numLeaves) (start + l.numLeaves) b := by
  have hl := l.numLeaves_pos
  let cut := start + l.numLeaves
  have hsplit : (∑ i ∈ Ico a (b - 1), treeGapWeight (.node () l r) start i) =
      (∑ i ∈ Ico a (cut - 1), treeGapWeight (.node () l r) start i) +
      (∑ i ∈ Ico (cut - 1) cut, treeGapWeight (.node () l r) start i) +
      (∑ i ∈ Ico cut (b - 1), treeGapWeight (.node () l r) start i) := by
    have h1 := (Finset.sum_Ico_consecutive (treeGapWeight (.node () l r) start)
      (m := a) (n := cut - 1) (k := b - 1) (by dsimp [cut]; omega) (by dsimp [cut]; omega)).symm
    have h2 := (Finset.sum_Ico_consecutive (treeGapWeight (.node () l r) start)
      (m := cut - 1) (n := cut) (k := b - 1) (by omega) (by dsimp [cut]; omega)).symm
    rw [h1, h2, Nat.add_assoc]
  have hsingleton : Ico (cut - 1) cut = {cut - 1} := by
    have he : (cut - 1) + 1 = cut := by dsimp [cut]; omega
    simpa only [he] using (Nat.Ico_succ_singleton (a := cut - 1))
  unfold treeIntervalSum
  rw [hsplit, hsingleton, Finset.sum_singleton, treeGapWeight_root]
  change treeIntervalSum (.node () l r) start a cut + l.numLeaves * r.numLeaves +
    treeIntervalSum (.node () l r) start cut b = _
  rw [treeIntervalSum_left l r start a cut (by rfl),
    treeIntervalSum_right l r start cut b (by rfl)]
  rfl

private theorem choose_two_add (a b : ℕ) :
    Nat.choose (a + b) 2 = Nat.choose a 2 + Nat.choose b 2 + a * b := by
  have succ (m : ℕ) : Nat.choose (m + 1) 2 = Nat.choose m 2 + m := by
    simpa [Nat.add_comm] using Nat.choose_succ_succ m 1
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + b = a + b + 1 by omega, succ, ih, succ]
    ring

/-- Every interval satisfies the associahedron supporting inequality. -/
theorem treeIntervalSum_lower (t : BinaryTree Unit) (start a b : ℕ)
    (ha : start ≤ a) (hab : a < b) (hb : b ≤ start + t.numLeaves) :
    Nat.choose (b - a) 2 ≤ treeIntervalSum t start a b := by
  induction t generalizing start a b with
  | nil =>
    simp only [BinaryTree.numLeaves] at hb
    have he : b - a = 1 := by omega
    simp [he, treeIntervalSum, treeGapWeight]
  | node _ l r il ir =>
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    simp only [BinaryTree.numLeaves] at hb
    by_cases hleft : b ≤ start + l.numLeaves
    · rw [treeIntervalSum_left l r start a b hleft]
      exact il start a b ha hab hleft
    by_cases hright : start + l.numLeaves ≤ a
    · rw [treeIntervalSum_right l r start a b hright]
      exact ir (start + l.numLeaves) a b hright hab (by omega)
    have hil := il start a (start + l.numLeaves) ha (by omega) (by omega)
    have hir := ir (start + l.numLeaves) (start + l.numLeaves) b (by omega) (by omega) (by omega)
    have he : b - a = (start + l.numLeaves - a) + (b - (start + l.numLeaves)) := by omega
    rw [treeIntervalSum_cross l r start a b (by omega) (by omega), he, choose_two_add]
    have hprod : (start + l.numLeaves - a) * (b - (start + l.numLeaves)) ≤
        l.numLeaves * r.numLeaves :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

/-- The sum of all gap coordinates is the fixed affine-hyperplane constant. -/
theorem treeIntervalSum_total (t : BinaryTree Unit) (start : ℕ) :
    treeIntervalSum t start start (start + t.numLeaves) = Nat.choose t.numLeaves 2 := by
  induction t generalizing start with
  | nil => simp [treeIntervalSum, treeGapWeight]
  | node _ l r il ir =>
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    simp only [BinaryTree.numLeaves]
    rw [treeIntervalSum_cross l r start start (start + (l.numLeaves + r.numLeaves))
      (by omega) (by omega), il,
      show start + (l.numLeaves + r.numLeaves) = (start + l.numLeaves) + r.numLeaves by omega,
      ir, choose_two_add]
    omega

/-- A subtree interval attains equality in its supporting inequality. -/
theorem treeIntervalSum_eq_of_mem (t : BinaryTree Unit) (start : ℕ) (p : BracketSpan)
    (hp : p ∈ treeSpans t start) :
    treeIntervalSum t start p.1 p.2 = Nat.choose (p.2 - p.1) 2 := by
  induction t generalizing start with
  | nil => simp [treeSpans] at hp
  | node _ l r il ir =>
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with rfl | hp | hp
    · have h := treeIntervalSum_total (.node () l r) start
      simpa only [BinaryTree.numLeaves, Nat.add_assoc, Nat.add_sub_cancel_left] using h
    · rw [treeIntervalSum_left l r start p.1 p.2 (treeSpans_valid l start p hp).2.2]
      exact il start hp
    · rw [treeIntervalSum_right l r start p.1 p.2 (treeSpans_valid r (start + l.numLeaves) p hp).1]
      exact ir (start + l.numLeaves) hp

/-- Equality holds exactly on the internal-node intervals. -/
theorem treeIntervalSum_eq_iff (t : BinaryTree Unit) (start : ℕ) (p : BracketSpan)
    (hv : SpanValid start t.numLeaves p) :
    treeIntervalSum t start p.1 p.2 = Nat.choose (p.2 - p.1) 2 ↔
      p ∈ treeSpans t start := by
  constructor
  · intro he
    induction t generalizing start with
    | nil => dsimp [SpanValid] at hv; omega
    | node _ l r il ir =>
      have hl := l.numLeaves_pos
      have hr := r.numLeaves_pos
      dsimp [SpanValid] at hv
      by_cases hleft : p.2 ≤ start + l.numLeaves
      · rw [treeIntervalSum_left l r start p.1 p.2 hleft] at he
        have hmem := il start (by dsimp [SpanValid]; omega) he
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hmem)
      by_cases hright : start + l.numLeaves ≤ p.1
      · rw [treeIntervalSum_right l r start p.1 p.2 hright] at he
        have hmem := ir (start + l.numLeaves) (by dsimp [SpanValid]; omega) he
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hmem)
      have hil := treeIntervalSum_lower l start p.1 (start + l.numLeaves) hv.1 (by omega) (by omega)
      have hir := treeIntervalSum_lower r (start + l.numLeaves) (start + l.numLeaves) p.2
        (by omega) (by omega) (by omega)
      have hend : p.2 - p.1 =
          (start + l.numLeaves - p.1) + (p.2 - (start + l.numLeaves)) := by omega
      rw [treeIntervalSum_cross l r start p.1 p.2 (by omega) (by omega), hend, choose_two_add] at he
      have hprod : l.numLeaves * r.numLeaves ≤
          (start + l.numLeaves - p.1) * (p.2 - (start + l.numLeaves)) := by omega
      have hx : start + l.numLeaves - p.1 ≤ l.numLeaves := by omega
      have hy : p.2 - (start + l.numLeaves) ≤ r.numLeaves := by omega
      have hp1 : (start + l.numLeaves - p.1) * (p.2 - (start + l.numLeaves)) ≤
          (start + l.numLeaves - p.1) * r.numLeaves := Nat.mul_le_mul_left _ hy
      have hp2 : (start + l.numLeaves - p.1) * (p.2 - (start + l.numLeaves)) ≤
          l.numLeaves * (p.2 - (start + l.numLeaves)) := Nat.mul_le_mul_right _ hx
      have hex : start + l.numLeaves - p.1 = l.numLeaves := by
        apply Nat.le_antisymm hx
        exact Nat.le_of_mul_le_mul_right (hprod.trans hp1) hr
      have hey : p.2 - (start + l.numLeaves) = r.numLeaves := by
        apply Nat.le_antisymm hy
        exact Nat.le_of_mul_le_mul_left (hprod.trans hp2) hl
      have heleft : p.1 = start := by omega
      have heright : p.2 = start + l.numLeaves + r.numLeaves := by omega
      have hp : p = (start, start + l.numLeaves + r.numLeaves) := Prod.ext heleft heright
      exact hp ▸ Finset.mem_insert_self _ _
  · exact treeIntervalSum_eq_of_mem t start p

/-- The real coordinate space for `K_(n+2)` has `n+1` gaps. -/
abbrev LodaySpace (n : ℕ) := Fin (n + 1) → ℝ

def lodayPoint (n : ℕ) (t : FullBracketing (n + 2)) : LodaySpace n :=
  fun i => treeGapWeight t.val 0 i.val

/-- The linear functional for one consecutive leaf interval. -/
def intervalLinear (n a b : ℕ) : LodaySpace n →ₗ[ℝ] ℝ :=
  ∑ i ∈ Ico a (b - 1), if h : i < n + 1 then LinearMap.proj ⟨i, h⟩ else 0

theorem lodayPoint_interval (n : ℕ) (t : FullBracketing (n + 2)) (a b : ℕ)
    (hb : b ≤ n + 2) :
    intervalLinear n a b (lodayPoint n t) = (treeIntervalSum t.val 0 a b : ℝ) := by
  simp only [intervalLinear, LinearMap.sum_apply, treeIntervalSum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_Ico.mp hi
  rw [dif_pos (by omega)]
  rfl

/-- The explicit convex hull of all binary-tree points. -/
def LodayPolytope (n : ℕ) : Set (LodaySpace n) :=
  convexHull ℝ (Set.range (lodayPoint n))

theorem LodayPolytope_convex (n : ℕ) : Convex ℝ (LodayPolytope n) :=
  convex_convexHull ℝ _

theorem LodayPolytope_compact (n : ℕ) : IsCompact (LodayPolytope n) :=
  (Set.finite_range (lodayPoint n)).isCompact_convexHull ℝ

theorem LodayPolytope_nonempty (n : ℕ) : (LodayPolytope n).Nonempty := by
  let t : FullBracketing (n + 2) := ⟨rightComb (n + 1), by simp⟩
  exact ⟨lodayPoint n t, subset_convexHull ℝ _ (Set.mem_range_self t)⟩

/-- The interval halfspace description to be compared with the convex hull. -/
def LodayHalfspaces (n : ℕ) : Set (LodaySpace n) :=
  {x | intervalLinear n 0 (n + 2) x = Nat.choose (n + 2) 2 ∧
    ∀ a b : ℕ, a < b → b ≤ n + 2 →
      (Nat.choose (b - a) 2 : ℝ) ≤ intervalLinear n a b x}

theorem LodayHalfspaces_convex (n : ℕ) : Convex ℝ (LodayHalfspaces n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · simp only [map_add, map_smul, smul_eq_mul, hx.1, hy.1]
    nlinarith
  · intro i j hij hj
    have hxi := hx.2 i j hij hj
    have hyi := hy.2 i j hij hj
    have h1 := mul_le_mul_of_nonneg_left hxi ha
    have h2 := mul_le_mul_of_nonneg_left hyi hb
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith

theorem lodayPoint_mem_halfspaces (n : ℕ) (t : FullBracketing (n + 2)) :
    lodayPoint n t ∈ LodayHalfspaces n := by
  constructor
  · rw [lodayPoint_interval n t 0 (n + 2) (by omega)]
    have ht := treeIntervalSum_total t.val 0
    simpa only [t.property, Nat.zero_add] using congrArg (fun v : ℕ => (v : ℝ)) ht
  · intro a b hab hb
    rw [lodayPoint_interval n t a b hb]
    exact_mod_cast treeIntervalSum_lower t.val 0 a b (by omega) hab
      (by simpa only [t.property, Nat.zero_add] using hb)

theorem LodayPolytope_subset_halfspaces (n : ℕ) :
    LodayPolytope n ⊆ LodayHalfspaces n :=
  convexHull_min (by rintro _ ⟨t, rfl⟩; exact lodayPoint_mem_halfspaces n t)
    (LodayHalfspaces_convex n)

theorem LodayPolytope_interval (n : ℕ) {x : LodaySpace n} (hx : x ∈ LodayPolytope n)
    (a b : ℕ) (hab : a < b) (hb : b ≤ n + 2) :
    (Nat.choose (b - a) 2 : ℝ) ≤ intervalLinear n a b x :=
  (LodayPolytope_subset_halfspaces n hx).2 a b hab hb

theorem LodayPolytope_total (n : ℕ) {x : LodaySpace n} (hx : x ∈ LodayPolytope n) :
    intervalLinear n 0 (n + 2) x = Nat.choose (n + 2) 2 :=
  (LodayPolytope_subset_halfspaces n hx).1

/-- Interval sums for arbitrary real gap coordinates. -/
def gapSum (w : ℕ → ℝ) (a b : ℕ) : ℝ := ∑ i ∈ Ico a (b - 1), w i

theorem gapSum_cross (w : ℕ → ℝ) (a cut b : ℕ) (ha : a < cut) (hb : cut < b) :
    gapSum w a b = gapSum w a cut + w (cut - 1) + gapSum w cut b := by
  have h1 := (Finset.sum_Ico_consecutive w (m := a) (n := cut - 1) (k := b - 1)
    (by omega) (by omega)).symm
  have h2 := (Finset.sum_Ico_consecutive w (m := cut - 1) (n := cut) (k := b - 1)
    (by omega) (by omega)).symm
  have hsingleton : Ico (cut - 1) cut = {cut - 1} := by
    have he : (cut - 1) + 1 = cut := by omega
    simpa only [he] using (Nat.Ico_succ_singleton (a := cut - 1))
  unfold gapSum
  rw [h1, h2, hsingleton, Finset.sum_singleton, add_assoc]

theorem gapSum_tree_total (t : BinaryTree Unit) (start : ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ treeSpans t start, gapSum w p.1 p.2 = Nat.choose (p.2 - p.1) 2) :
    gapSum w start (start + t.numLeaves) = Nat.choose t.numLeaves 2 := by
  cases t with
  | nil => simp [gapSum]
  | node _ l r =>
    have h := hw (start, start + l.numLeaves + r.numLeaves) (Finset.mem_insert_self _ _)
    simpa only [BinaryTree.numLeaves, Nat.add_assoc, Nat.add_sub_cancel_left] using h

/-- The tight tree intervals uniquely determine all gap coordinates. -/
theorem gapCoordinates_unique (t : BinaryTree Unit) (start : ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ treeSpans t start, gapSum w p.1 p.2 = Nat.choose (p.2 - p.1) 2)
    (i : ℕ) (hi : start ≤ i ∧ i < start + t.numLeaves - 1) :
    w i = (treeGapWeight t start i : ℝ) := by
  induction t generalizing start with
  | nil => simp only [BinaryTree.numLeaves] at hi; omega
  | node _ l r il ir =>
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    have hwl : ∀ p ∈ treeSpans l start,
        gapSum w p.1 p.2 = Nat.choose (p.2 - p.1) 2 := by
      intro p hp; exact hw p (Finset.mem_insert_of_mem (Finset.mem_union_left _ hp))
    have hwr : ∀ p ∈ treeSpans r (start + l.numLeaves),
        gapSum w p.1 p.2 = Nat.choose (p.2 - p.1) 2 := by
      intro p hp; exact hw p (Finset.mem_insert_of_mem (Finset.mem_union_right _ hp))
    by_cases hleft : i < start + l.numLeaves - 1
    · have hh := il start hwl ⟨hi.1, hleft⟩
      have hz := treeGapWeight_support r (start + l.numLeaves) i (Or.inl (by omega))
      simp only [treeGapWeight, hz, if_neg (by omega : i ≠ start + l.numLeaves - 1), Nat.add_zero]
      exact hh
    by_cases hright : start + l.numLeaves ≤ i
    · have hh := ir (start + l.numLeaves) hwr (by simp only [BinaryTree.numLeaves] at hi; omega)
      have hz := treeGapWeight_support l start i (Or.inr (by omega))
      simp only [treeGapWeight, hz, if_neg (by omega : i ≠ start + l.numLeaves - 1), Nat.zero_add,
        Nat.add_zero]
      exact hh
    have he : i = start + l.numLeaves - 1 := by omega
    rw [he, treeGapWeight_root]
    have htotal := gapSum_tree_total (.node () l r) start w hw
    have hltotal := gapSum_tree_total l start w hwl
    have hrtotal := gapSum_tree_total r (start + l.numLeaves) w hwr
    simp only [BinaryTree.numLeaves] at htotal
    rw [gapSum_cross w start (start + l.numLeaves) (start + (l.numLeaves + r.numLeaves))
      (by omega) (by omega), hltotal,
      show start + (l.numLeaves + r.numLeaves) = (start + l.numLeaves) + r.numLeaves by omega,
      hrtotal] at htotal
    have hc := congrArg (fun m : ℕ => (m : ℝ)) (choose_two_add l.numLeaves r.numLeaves)
    push_cast at hc ⊢
    linarith

def coordinateAt (n : ℕ) (x : LodaySpace n) (i : ℕ) : ℝ :=
  if h : i < n + 1 then x ⟨i, h⟩ else 0

theorem gapSum_coordinateAt (n : ℕ) (x : LodaySpace n) (a b : ℕ) :
    gapSum (coordinateAt n x) a b = intervalLinear n a b x := by
  simp only [gapSum, intervalLinear, LinearMap.sum_apply, coordinateAt]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

theorem lodayPoint_unique (n : ℕ) (t : FullBracketing (n + 2)) (x : LodaySpace n)
    (hx : ∀ p ∈ treeSpans t.val 0,
      intervalLinear n p.1 p.2 x = Nat.choose (p.2 - p.1) 2) : x = lodayPoint n t := by
  funext i
  have hw : ∀ p ∈ treeSpans t.val 0,
      gapSum (coordinateAt n x) p.1 p.2 = Nat.choose (p.2 - p.1) 2 := by
    intro p hp; rw [gapSum_coordinateAt]; exact hx p hp
  have h := gapCoordinates_unique t.val 0 (coordinateAt n x) hw i.val (by
    simp only [t.property, Nat.zero_add]; have hi := i.isLt; omega)
  simpa only [coordinateAt, dif_pos i.isLt, lodayPoint] using h

theorem lodayPoint_injective (n : ℕ) : Function.Injective (lodayPoint n) := by
  intro t u he
  apply Subtype.ext
  apply treeSpans_injective t.val u.val 0 (t.property.trans u.property.symm)
  have hsub : treeSpans t.val 0 ⊆ treeSpans u.val 0 := by
    intro p hp
    have hv := treeSpans_valid t.val 0 p hp
    have hb : p.2 ≤ n + 2 := by have h := hv.2.2; simpa only [t.property, Nat.zero_add] using h
    have hv' : SpanValid 0 u.val.numLeaves p := by simpa only [t.property, u.property] using hv
    apply (treeIntervalSum_eq_iff u.val 0 p hv').mp
    have ht := congrArg (fun m : ℕ => (m : ℝ)) (treeIntervalSum_eq_of_mem t.val 0 p hp)
    rw [← lodayPoint_interval n t p.1 p.2 hb, he, lodayPoint_interval n u p.1 p.2 hb] at ht
    exact_mod_cast ht
  apply Finset.eq_of_subset_of_card_le hsub
  rw [treeSpans_card, treeSpans_card]
  have ht := t.val.numLeaves_eq_numNodes_succ
  have hu := u.val.numLeaves_eq_numNodes_succ
  rw [t.property] at ht
  rw [u.property] at hu
  omega

/-- Every tree point is an actual extreme point of the convex hull. -/
theorem lodayPoint_extreme (n : ℕ) (t : FullBracketing (n + 2)) :
    lodayPoint n t ∈ (LodayPolytope n).extremePoints ℝ := by
  constructor
  · exact subset_convexHull ℝ _ (Set.mem_range_self t)
  · intro x hx y hy hz
    obtain ⟨a, b, ha, hb, hab, he⟩ := hz
    apply lodayPoint_unique n t x
    intro p hp
    have hv := treeSpans_valid t.val 0 p hp
    have hpab : p.1 < p.2 := by have h := hv.2.1; omega
    have hpb : p.2 ≤ n + 2 := by simpa only [t.property, Nat.zero_add] using hv.2.2
    have hxp := LodayPolytope_interval n hx p.1 p.2 hpab hpb
    have hyp := LodayPolytope_interval n hy p.1 p.2 hpab hpb
    have ht := congrArg (fun m : ℕ => (m : ℝ)) (treeIntervalSum_eq_of_mem t.val 0 p hp)
    rw [← lodayPoint_interval n t p.1 p.2 hpb] at ht
    have hlin := congrArg (intervalLinear n p.1 p.2) he
    simp only [map_add, map_smul, smul_eq_mul, ht] at hlin
    have hmul := mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hyp)
    nlinarith

/-- There are no other vertices of the convex hull. -/
theorem LodayPolytope_extremePoints (n : ℕ) :
    (LodayPolytope n).extremePoints ℝ = Set.range (lodayPoint n) := by
  apply Set.Subset.antisymm
  · exact extremePoints_convexHull_subset
  · rintro _ ⟨t, rfl⟩
    exact lodayPoint_extreme n t

/-- Binary trees classify the vertices of the explicit convex polytope. -/
noncomputable def fullBracketing_loday_vertex_equiv (n : ℕ) :
    FullBracketing (n + 2) ≃ ↥((LodayPolytope n).extremePoints ℝ) := by
  rw [LodayPolytope_extremePoints]
  exact Equiv.ofInjective (lodayPoint n) (lodayPoint_injective n)

end FunctorialGeometry
