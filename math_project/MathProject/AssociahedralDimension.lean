/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralFaces
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Atoms

/-! # Affine dimension and geometric facet count -/

namespace FunctorialGeometry

open Finset AffineSubspace

noncomputable def LodayAffineDimension (n : ℕ) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (LodayPolytope n)).direction

noncomputable def LodayFaceDimension (n : ℕ) (F : LodayExposedFace n) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ F.val).direction

/-- Proper containment of supporting faces strictly increases affine dimension. -/
theorem LodayFaceDimension_strict (n : ℕ) {F G : LodayExposedFace n} (h : F < G) :
    LodayFaceDimension n F < LodayFaceDimension n G := by
  obtain ⟨f, hf⟩ := F.property.2
  obtain ⟨x, hx⟩ := F.property.1
  have hsub : F.val ⊆ G.val := le_of_lt h
  have hneq : F.val ≠ G.val := by
    intro he; exact (ne_of_lt h) (Subtype.ext he)
  have hy : ∃ y ∈ G.val, y ∉ F.val := by
    by_contra hn
    apply hneq
    apply Set.Subset.antisymm hsub
    intro y hy
    by_contra hy'
    exact hn ⟨y, hy, hy'⟩
  obtain ⟨y, hy, hnot⟩ := hy
  let level := (affineSpan ℝ ({f x} : Set ℝ)).comap f.toAffineMap
  have hFlevel : affineSpan ℝ F.val ≤ level := by
    apply affineSpan_le.mpr
    intro z hz
    apply AffineSubspace.mem_comap.mpr
    apply (AffineSubspace.mem_affineSpan_singleton ℝ ℝ).mpr
    exact le_antisymm (((hf z).mp hz).2 x ((hf x).mp hx).1)
      (((hf x).mp hx).2 z ((hf z).mp hz).1)
  have hspanlt : affineSpan ℝ F.val < affineSpan ℝ G.val := by
    apply lt_of_le_of_ne (affineSpan_mono ℝ hsub)
    intro he
    have hylevel : y ∈ level := hFlevel (he.symm ▸ mem_affineSpan ℝ hy)
    have heq : f y = f x := (AffineSubspace.mem_affineSpan_singleton ℝ ℝ).mp
      (AffineSubspace.mem_comap.mp hylevel)
    have hyP := ((G.property.2.choose_spec y).mp hy).1
    apply hnot
    apply (hf y).mpr
    exact ⟨hyP, fun z hz => by simpa only [heq] using ((hf x).mp hx).2 z hz⟩
  exact Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty hspanlt (F.property.1.affineSpan ℝ))

theorem intervalLinear_total_sum (n : ℕ) (x : LodaySpace n) :
    intervalLinear n 0 (n + 2) x = ∑ i : Fin (n + 1), x i := by
  rw [← gapSum_coordinateAt]
  unfold gapSum
  simp only [show n + 2 - 1 = n + 1 by omega, Nat.Ico_zero_eq_range]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coordinateAt, dif_pos i.isLt]

theorem LodayAffineDimension_le (n : ℕ) : LodayAffineDimension n ≤ n := by
  let f := intervalLinear n 0 (n + 2)
  have hsurj : Function.Surjective f := by
    intro r
    refine ⟨fun i => if i = 0 then r else 0, ?_⟩
    rw [intervalLinear_total_sum]
    simp
  have hk := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_self, Module.finrank_pi, Fintype.card_fin] at hk
  have hdir : (affineSpan ℝ (LodayPolytope n)).direction ≤ f.ker := by
    rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro v ⟨x, hx, y, hy, rfl⟩
    change f (x - y) = 0
    rw [map_sub]
    change intervalLinear n 0 (n + 2) x - intervalLinear n 0 (n + 2) y = 0
    rw [LodayPolytope_total n hx, LodayPolytope_total n hy, sub_self]
  have hd := Submodule.finrank_mono hdir
  unfold LodayAffineDimension
  have hker : Module.finrank ℝ f.ker = n := Nat.add_left_cancel (hk.trans (Nat.add_comm n 1))
  exact hd.trans hker.le

/-- Removing one bracket gives a strict chain step in the geometric face order. -/
theorem Loday_dimension_chain_bound (n : ℕ) (s : Finset (ProperBracket (n + 2)))
    (hs : ∀ a ∈ s, ∀ b ∈ s, BracketCompatible a b) :
    s.card + LodayFaceDimension n (bracketExposedFace n ⟨s, hs⟩) ≤ LodayAffineDimension n := by
  induction s using Finset.induction_on with
  | empty =>
    have he : (bracketExposedFace n ⟨∅, hs⟩).val = LodayPolytope n := by
      ext x; simp [bracketExposedFace, LodayBracketFace]
    simp only [Finset.card_empty, Nat.zero_add]
    unfold LodayFaceDimension LodayAffineDimension
    rw [he]
  | @insert a s ha ih =>
    have hs' : ∀ b ∈ s, ∀ c ∈ s, BracketCompatible b c := by
      intro b hb c hc
      exact hs b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc)
    have hih := ih hs'
    let p : PartialBracketing (n + 2) := ⟨insert a s, hs⟩
    let q : PartialBracketing (n + 2) := ⟨s, hs'⟩
    have hpq : p < q := by
      change s ⊂ insert a s
      exact Finset.ssubset_insert ha
    have hfaces : bracketExposedFace n p < bracketExposedFace n q :=
      (partialBracketing_loday_orderIso n).strictMono hpq
    have hd := LodayFaceDimension_strict n hfaces
    rw [Finset.card_insert_of_notMem ha]
    dsimp [p, q] at hd
    omega

/-- The actual affine dimension of the convex polytope `K_(n+2)` is `n`. -/
theorem Loday_affine_dimension (n : ℕ) : LodayAffineDimension n = n := by
  apply le_antisymm (LodayAffineDimension_le n)
  let t : FullBracketing (n + 2) := ⟨rightComb (n + 1), by simp⟩
  let p := treePartialBracketing t
  have hc : p.val.card = n := by
    simpa using treeProperSpans_card (by omega : 2 ≤ n + 2) t
  have h := Loday_dimension_chain_bound n p.val p.property
  rw [hc] at h
  omega

def wholeLodayFace (n : ℕ) : LodayExposedFace n :=
  ⟨LodayPolytope n, LodayPolytope_nonempty n, 0, by simp⟩

instance (n : ℕ) : OrderTop (LodayExposedFace n) where
  top := wholeLodayFace n
  le_top F := by
    intro x hx
    exact ((F.property.2.choose_spec x).mp hx).1

instance (n : ℕ) : OrderTop (NoncrossingFace n) where
  top := wholePolygonFace n
  le_top _ := Finset.empty_subset _

theorem polygonFacet_iff_isCoatom {n : ℕ} (p : NoncrossingFace n) :
    IsPolygonFacet p ↔ IsCoatom p := by
  rw [isCoatom_iff_ge_of_le]
  constructor
  · rintro ⟨hne, hmax⟩
    constructor
    · intro he
      have hval := congrArg Subtype.val he
      exact hne.ne_empty hval
    · intro q hq hpq
      rcases hmax q hpq with he | he
      · rw [he]
      · exact False.elim (hq (Subtype.ext he))
  · rintro ⟨hne, hmax⟩
    constructor
    · by_contra h
      exact hne (Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp h))
    · intro q hpq
      by_cases hq : q = ⊤
      · right; exact congrArg Subtype.val hq
      · left; exact le_antisymm (hmax q hq hpq) hpq

noncomputable def polygonFacet_lodayFacet_equiv (n : ℕ) :
    {p : NoncrossingFace (n + 2) // IsPolygonFacet p} ≃
      {F : LodayExposedFace n // IsCoatom F} :=
  (polygon_loday_face_orderIso n).toEquiv.subtypeEquiv (fun p =>
    (polygonFacet_iff_isCoatom p).trans ((polygon_loday_face_orderIso n).isCoatom_iff p).symm)

noncomputable instance (n : ℕ) : Fintype {F : LodayExposedFace n // IsCoatom F} :=
  Fintype.ofEquiv _ (polygonFacet_lodayFacet_equiv n)

/-- The geometric facet count for the convex realization, in every dimension. -/
theorem Loday_geometric_facet_count (n : ℕ) :
    Fintype.card {F : LodayExposedFace n // IsCoatom F} = n * (n + 3) / 2 := by
  rw [← Fintype.card_congr (polygonFacet_lodayFacet_equiv n), Kn_facet_count]

noncomputable instance (n : ℕ) : Fintype ↥((LodayPolytope n).extremePoints ℝ) :=
  Fintype.ofEquiv _ (fullBracketing_loday_vertex_equiv n)

/-- The Catalan number counts the actual extreme points of the convex hull. -/
theorem Loday_geometric_vertex_count (n : ℕ) :
    Fintype.card ↥((LodayPolytope n).extremePoints ℝ) = catalan (n + 1) := by
  rw [← Fintype.card_congr (fullBracketing_loday_vertex_equiv n), fullBracketing_card]

theorem Loday_geometric_vertex_count_formula (n : ℕ) :
    Fintype.card ↥((LodayPolytope n).extremePoints ℝ) =
      Nat.choose (2 * (n + 1)) (n + 1) / (n + 2) := by
  rw [Loday_geometric_vertex_count, catalan_eq_centralBinom_div]
  rfl

/-- The geometric face family with the same nullary and unary conventions. -/
def KnGeometricFace : ℕ → Type
  | 0 => Empty
  | 1 => Unit
  | n + 2 => LodayExposedFace n

instance (n : ℕ) : PartialOrder (KnGeometricFace n) := by
  cases n with
  | zero => unfold KnGeometricFace; infer_instance
  | succ n => cases n <;> unfold KnGeometricFace <;> infer_instance

/-- All `K_n`: the polygon model agrees with the convex supporting-face model. -/
noncomputable def all_Kn_geometric_orderIso : (n : ℕ) → KnFace n ≃o KnGeometricFace n
  | 0 => OrderIso.refl Empty
  | 1 =>
    { toEquiv := K1_equiv_unit
      map_rel_iff' := by
        intro a b
        constructor
        · intro _
          have he : a = b := K1_equiv_unit.injective (Subsingleton.elim _ _)
          rw [he]
        · intro _; change (() : Unit) ≤ (); exact le_rfl }
  | n + 2 => polygon_loday_face_orderIso n

/-- The complete family starting at `K₂`, evaluated on any poset chain.
Here `n` is the dimension and the associahedron is `K_(n+2)`. -/
theorem all_Kn_poset_realization {L : Type*} [PartialOrder L] (n : ℕ)
    (x : Fin (n + 3) → L) (hx : Monotone x) :
    Nonempty (KnFace (n + 2) ≃o LodayExposedFace n) ∧
      Convex ℝ (LodayPolytope n) ∧ IsCompact (LodayPolytope n) ∧
      LodayAffineDimension n = n ∧
      Fintype.card ↥((LodayPolytope n).extremePoints ℝ) = catalan (n + 1) ∧
      Fintype.card {F : LodayExposedFace n // IsCoatom F} = n * (n + 3) / 2 ∧
      ∀ s t : FullBracketing (n + 2), evalChainBracketing x hx s = evalChainBracketing x hx t :=
  ⟨⟨polygon_loday_face_orderIso n⟩, LodayPolytope_convex n, LodayPolytope_compact n,
    Loday_affine_dimension n, Loday_geometric_vertex_count n, Loday_geometric_facet_count n,
    fun s t => all_Kn_chain_composites x hx s t⟩

end FunctorialGeometry
