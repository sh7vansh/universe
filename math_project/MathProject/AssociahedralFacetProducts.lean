/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralDimension

/-! # Facets as products of smaller associahedra

A fixed polygon diagonal cuts the polygon into two smaller polygons. The nonempty
subfaces of its facet have the product of the two smaller nonempty face orders.
This is a combinatorial product statement, transferred to actual supporting faces.
-/

namespace FunctorialGeometry

/-- Arity of the polygon on the consecutive side of a diagonal. -/
def facetLeftArity {n : ℕ} (d : PolygonDiagonal n) : ℕ := d.b.val - d.a.val

/-- Arity of the polygon on the complementary side of a diagonal. -/
def facetRightArity {n : ℕ} (d : PolygonDiagonal n) : ℕ :=
  n - facetLeftArity d + 1

theorem facet_arities {n : ℕ} (d : PolygonDiagonal n) :
    2 ≤ facetLeftArity d ∧ 2 ≤ facetRightArity d ∧
      facetLeftArity d + facetRightArity d = n + 1 := by
  have hg := d.gap
  have hb := d.b.isLt
  have hn := d.not_boundary
  dsimp [facetLeftArity, facetRightArity]
  omega

private def facetLeftDiagonal {n : ℕ} (d : PolygonDiagonal n)
    (e : PolygonDiagonal (facetLeftArity d)) : PolygonDiagonal n where
  a := ⟨d.a.val + e.a.val, by
    have h := e.a.isLt; have h' := d.b.isLt
    dsimp [facetLeftArity] at h; omega⟩
  b := ⟨d.a.val + e.b.val, by
    have h := e.b.isLt; have h' := d.b.isLt
    dsimp [facetLeftArity] at h; omega⟩
  gap := by have h := e.gap; dsimp; omega
  not_boundary := by
    have h := e.b.isLt; have h' := d.not_boundary
    dsimp [facetLeftArity] at h
    dsimp; omega

private def facetRightVertex {n : ℕ} (d : PolygonDiagonal n)
    (i : Fin (facetRightArity d + 1)) : Fin (n + 1) :=
  ⟨if i.val ≤ d.a.val then i.val else i.val + (facetLeftArity d - 1), by
    have hi := i.isLt
    have ha := d.a.isLt
    have hg := d.gap
    have hb := d.b.isLt
    dsimp [facetRightArity, facetLeftArity] at *
    split_ifs <;> omega⟩

private theorem facetRightVertex_lt_iff {n : ℕ} (d : PolygonDiagonal n)
    (i j : Fin (facetRightArity d + 1)) :
    (facetRightVertex d i).val < (facetRightVertex d j).val ↔ i.val < j.val := by
  have hg := d.gap
  dsimp [facetRightVertex, facetLeftArity]
  split_ifs <;> omega

private theorem facetRightVertex_injective {n : ℕ} (d : PolygonDiagonal n) :
    Function.Injective (facetRightVertex d) := by
  intro i j h
  have he := congrArg Fin.val h
  have hg := d.gap
  apply Fin.ext
  dsimp [facetRightVertex, facetLeftArity] at he
  split_ifs at he <;> omega

private def facetRightDiagonal {n : ℕ} (d : PolygonDiagonal n)
    (e : PolygonDiagonal (facetRightArity d)) : PolygonDiagonal n where
  a := facetRightVertex d e.a
  b := facetRightVertex d e.b
  gap := by
    have h := e.gap; have hg := d.gap
    dsimp [facetRightVertex, facetLeftArity]
    split_ifs <;> omega
  not_boundary := by
    have h := e.not_boundary
    have hb := e.b.isLt
    have hg := d.gap; have hd := d.b.isLt
    dsimp [facetRightArity, facetLeftArity] at h hb
    dsimp [facetRightVertex, facetLeftArity]
    split_ifs <;> omega

private theorem facetLeftDiagonal_injective {n : ℕ} (d : PolygonDiagonal n) :
    Function.Injective (facetLeftDiagonal d) := by
  intro e f h
  have ha := congrArg (fun q => q.a.val) h
  have hb := congrArg (fun q => q.b.val) h
  apply PolygonDiagonal.ext <;> apply Fin.ext
  · dsimp [facetLeftDiagonal] at ha; omega
  · dsimp [facetLeftDiagonal] at hb; omega

private theorem facetRightDiagonal_injective {n : ℕ} (d : PolygonDiagonal n) :
    Function.Injective (facetRightDiagonal d) := by
  intro e f h
  apply PolygonDiagonal.ext
  · exact facetRightVertex_injective d (congrArg PolygonDiagonal.a h)
  · exact facetRightVertex_injective d (congrArg PolygonDiagonal.b h)

private theorem facetLeftDiagonal_cross_iff {n : ℕ} (d : PolygonDiagonal n)
    (e f : PolygonDiagonal (facetLeftArity d)) :
    DiagonalsCross (facetLeftDiagonal d e) (facetLeftDiagonal d f) ↔ DiagonalsCross e f := by
  dsimp [DiagonalsCross, facetLeftDiagonal]
  omega

private theorem facetRightDiagonal_cross_iff {n : ℕ} (d : PolygonDiagonal n)
    (e f : PolygonDiagonal (facetRightArity d)) :
    DiagonalsCross (facetRightDiagonal d e) (facetRightDiagonal d f) ↔ DiagonalsCross e f := by
  simp only [DiagonalsCross, facetRightDiagonal, facetRightVertex_lt_iff]

private theorem facetLeftDiagonal_ne {n : ℕ} (d : PolygonDiagonal n)
    (e : PolygonDiagonal (facetLeftArity d)) : facetLeftDiagonal d e ≠ d := by
  intro he
  have ha := congrArg (fun q => q.a.val) he
  have hb := congrArg (fun q => q.b.val) he
  have hn := e.not_boundary
  have hg := d.gap
  dsimp [facetLeftDiagonal] at ha hb
  dsimp [facetLeftArity] at hn
  omega

private theorem facetRightDiagonal_ne {n : ℕ} (d : PolygonDiagonal n)
    (e : PolygonDiagonal (facetRightArity d)) : facetRightDiagonal d e ≠ d := by
  intro he
  have ha := congrArg (fun q => q.a.val) he
  have hb := congrArg (fun q => q.b.val) he
  have hg := e.gap; have hd := d.gap
  dsimp [facetRightDiagonal, facetRightVertex, facetLeftArity] at ha hb
  split_ifs at ha hb <;> omega

private theorem facetLeftDiagonal_compatible {n : ℕ} (d : PolygonDiagonal n)
    (e : PolygonDiagonal (facetLeftArity d)) : ¬ DiagonalsCross d (facetLeftDiagonal d e) := by
  have ha := e.a.isLt; have hb := e.b.isLt; have hg := d.gap
  dsimp [facetLeftArity] at ha hb
  dsimp [DiagonalsCross, facetLeftDiagonal]
  omega

private theorem facetRightDiagonal_compatible {n : ℕ} (d : PolygonDiagonal n)
    (e : PolygonDiagonal (facetRightArity d)) : ¬ DiagonalsCross d (facetRightDiagonal d e) := by
  have hg := e.gap; have hd := d.gap
  dsimp [DiagonalsCross, facetRightDiagonal, facetRightVertex, facetLeftArity]
  split_ifs <;> omega

private theorem facetSides_disjoint {n : ℕ} (d : PolygonDiagonal n)
    (e : PolygonDiagonal (facetLeftArity d)) (f : PolygonDiagonal (facetRightArity d)) :
    facetLeftDiagonal d e ≠ facetRightDiagonal d f := by
  intro he
  have ha := congrArg (fun q => q.a.val) he
  have hb := congrArg (fun q => q.b.val) he
  have hne := e.not_boundary; have he := e.gap; have hf := f.gap
  have heb := e.b.isLt; have hd := d.gap
  dsimp [facetLeftArity] at hne heb
  dsimp [facetLeftDiagonal, facetRightDiagonal, facetRightVertex, facetLeftArity] at ha hb
  split_ifs at ha hb <;> omega

private theorem facetSides_noncrossing {n : ℕ} (d : PolygonDiagonal n)
    (e : PolygonDiagonal (facetLeftArity d)) (f : PolygonDiagonal (facetRightArity d)) :
    ¬ DiagonalsCross (facetLeftDiagonal d e) (facetRightDiagonal d f) := by
  have heb := e.b.isLt; have he := e.gap; have hd := d.gap; have hf := f.gap
  dsimp [facetLeftArity] at heb
  dsimp [DiagonalsCross, facetLeftDiagonal, facetRightDiagonal, facetRightVertex, facetLeftArity]
  split_ifs <;> omega

private theorem facetDiagonal_sides {n : ℕ} (d e : PolygonDiagonal n)
    (hne : e ≠ d) (hc : ¬ DiagonalsCross d e) :
    (∃ f : PolygonDiagonal (facetLeftArity d), facetLeftDiagonal d f = e) ∨
      (∃ f : PolygonDiagonal (facetRightArity d), facetRightDiagonal d f = e) := by
  have hd := d.gap
  have hdb := d.b.isLt
  have hg := e.gap
  have hb := e.b.isLt
  have hn := e.not_boundary
  by_cases hi : d.a.val ≤ e.a.val ∧ e.b.val ≤ d.b.val
  · left
    let f : PolygonDiagonal (facetLeftArity d) :=
      { a := ⟨e.a.val - d.a.val, by dsimp [facetLeftArity]; omega⟩
        b := ⟨e.b.val - d.a.val, by dsimp [facetLeftArity]; omega⟩
        gap := by dsimp; omega
        not_boundary := by
          intro hf
          dsimp [facetLeftArity] at hf
          apply hne
          apply PolygonDiagonal.ext <;> apply Fin.ext <;> omega }
    refine ⟨f, ?_⟩
    apply PolygonDiagonal.ext <;> apply Fin.ext <;> dsimp [f, facetLeftDiagonal] <;> omega
  · right
    have haout : e.a.val ≤ d.a.val ∨ d.b.val ≤ e.a.val := by
      dsimp [DiagonalsCross] at hc; omega
    have hbout : e.b.val ≤ d.a.val ∨ d.b.val ≤ e.b.val := by
      dsimp [DiagonalsCross] at hc; omega
    let ca := if e.a.val ≤ d.a.val then e.a.val else e.a.val - (facetLeftArity d - 1)
    let cb := if e.b.val ≤ d.a.val then e.b.val else e.b.val - (facetLeftArity d - 1)
    let f : PolygonDiagonal (facetRightArity d) :=
      { a := ⟨ca, by
          dsimp [ca, facetRightArity, facetLeftArity]
          split_ifs <;> omega⟩
        b := ⟨cb, by
          dsimp [cb, facetRightArity, facetLeftArity]
          split_ifs <;> omega⟩
        gap := by
          dsimp [ca, cb, facetLeftArity]
          split_ifs <;> omega
        not_boundary := by
          dsimp [ca, cb, facetRightArity, facetLeftArity]
          split_ifs <;> omega }
    refine ⟨f, ?_⟩
    apply PolygonDiagonal.ext <;> apply Fin.ext
    · dsimp [f, ca, facetRightDiagonal, facetRightVertex, facetLeftArity]
      split_ifs <;> omega
    · dsimp [f, cb, facetRightDiagonal, facetRightVertex, facetLeftArity]
      split_ifs <;> omega

/-- The nonempty subfaces of the facet indexed by `d`. -/
abbrev PolygonFacetFaces {n : ℕ} (d : PolygonDiagonal n) :=
  {p : NoncrossingFace n // d ∈ p.val}

theorem mem_diagonal_iff_le_facet {n : ℕ} (d : PolygonDiagonal n)
    (p : NoncrossingFace n) : d ∈ p.val ↔ p ≤ singletonPolygonFace d := by
  exact Finset.singleton_subset_iff.symm

private def facetLeftEmbedding {n : ℕ} (d : PolygonDiagonal n) :
    PolygonDiagonal (facetLeftArity d) ↪ PolygonDiagonal n :=
  ⟨facetLeftDiagonal d, facetLeftDiagonal_injective d⟩

private def facetRightEmbedding {n : ℕ} (d : PolygonDiagonal n) :
    PolygonDiagonal (facetRightArity d) ↪ PolygonDiagonal n :=
  ⟨facetRightDiagonal d, facetRightDiagonal_injective d⟩

private def joinFacetDiagonals {n : ℕ} (d : PolygonDiagonal n)
    (p : NoncrossingFace (facetLeftArity d) × NoncrossingFace (facetRightArity d)) :
    Finset (PolygonDiagonal n) :=
  insert d (p.1.val.map (facetLeftEmbedding d) ∪ p.2.val.map (facetRightEmbedding d))

private theorem mem_joinFacetDiagonals {n : ℕ} (d e : PolygonDiagonal n)
    (p : NoncrossingFace (facetLeftArity d) × NoncrossingFace (facetRightArity d)) :
    e ∈ joinFacetDiagonals d p ↔ e = d ∨
      (∃ f ∈ p.1.val, facetLeftDiagonal d f = e) ∨
      (∃ f ∈ p.2.val, facetRightDiagonal d f = e) := by
  simp [joinFacetDiagonals, facetLeftEmbedding, facetRightEmbedding, Finset.mem_map]

private theorem diagonalsCross_comm {n : ℕ} (d e : PolygonDiagonal n) :
    DiagonalsCross d e ↔ DiagonalsCross e d := by
  simp only [DiagonalsCross, or_comm]

private def joinFacetFaces {n : ℕ} (d : PolygonDiagonal n)
    (p : NoncrossingFace (facetLeftArity d) × NoncrossingFace (facetRightArity d)) :
    PolygonFacetFaces d :=
  ⟨⟨joinFacetDiagonals d p, by
    intro e he f hf
    rw [mem_joinFacetDiagonals] at he hf
    rcases he with he | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · subst e
      rcases hf with hf | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
      · subst f; simp [DiagonalsCross]
      · exact facetLeftDiagonal_compatible d f
      · exact facetRightDiagonal_compatible d f
    · rcases hf with hf | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
      · subst f
        exact fun h => facetLeftDiagonal_compatible d e ((diagonalsCross_comm _ _).mp h)
      · exact (facetLeftDiagonal_cross_iff d e f).not.mpr (p.1.property e he f hf)
      · exact facetSides_noncrossing d e f
    · rcases hf with hf | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
      · subst f
        exact fun h => facetRightDiagonal_compatible d e ((diagonalsCross_comm _ _).mp h)
      · exact fun h => facetSides_noncrossing d f e ((diagonalsCross_comm _ _).mp h)
      · exact (facetRightDiagonal_cross_iff d e f).not.mpr (p.2.property e he f hf)⟩,
    by simp [joinFacetDiagonals]⟩

private theorem left_mem_join {n : ℕ} (d : PolygonDiagonal n)
    (p : NoncrossingFace (facetLeftArity d) × NoncrossingFace (facetRightArity d))
    (e : PolygonDiagonal (facetLeftArity d)) :
    facetLeftDiagonal d e ∈ (joinFacetFaces d p).val.val ↔ e ∈ p.1.val := by
  rw [show (joinFacetFaces d p).val.val = joinFacetDiagonals d p from rfl,
    mem_joinFacetDiagonals]
  constructor
  · rintro (he | ⟨f, hf, he⟩ | ⟨f, hf, he⟩)
    · exact False.elim (facetLeftDiagonal_ne d e he)
    · exact facetLeftDiagonal_injective d he ▸ hf
    · exact False.elim (facetSides_disjoint d e f he.symm)
  · intro he; exact Or.inr (Or.inl ⟨e, he, rfl⟩)

private theorem right_mem_join {n : ℕ} (d : PolygonDiagonal n)
    (p : NoncrossingFace (facetLeftArity d) × NoncrossingFace (facetRightArity d))
    (e : PolygonDiagonal (facetRightArity d)) :
    facetRightDiagonal d e ∈ (joinFacetFaces d p).val.val ↔ e ∈ p.2.val := by
  rw [show (joinFacetFaces d p).val.val = joinFacetDiagonals d p from rfl,
    mem_joinFacetDiagonals]
  constructor
  · rintro (he | ⟨f, hf, he⟩ | ⟨f, hf, he⟩)
    · exact False.elim (facetRightDiagonal_ne d e he)
    · exact False.elim (facetSides_disjoint d f e he)
    · exact facetRightDiagonal_injective d he ▸ hf
  · intro he; exact Or.inr (Or.inr ⟨e, he, rfl⟩)

private theorem joinFacetFaces_le_iff {n : ℕ} (d : PolygonDiagonal n)
    (p q : NoncrossingFace (facetLeftArity d) × NoncrossingFace (facetRightArity d)) :
    joinFacetFaces d p ≤ joinFacetFaces d q ↔ p ≤ q := by
  change joinFacetDiagonals d q ⊆ joinFacetDiagonals d p ↔
    q.1.val ⊆ p.1.val ∧ q.2.val ⊆ p.2.val
  constructor
  · intro h
    constructor
    · intro e he
      exact (left_mem_join d p e).mp (h ((left_mem_join d q e).mpr he))
    · intro e he
      exact (right_mem_join d p e).mp (h ((right_mem_join d q e).mpr he))
  · rintro ⟨hl, hr⟩ e he
    rw [mem_joinFacetDiagonals] at he ⊢
    rcases he with he | ⟨f, hf, he⟩ | ⟨f, hf, he⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨f, hl hf, he⟩)
    · exact Or.inr (Or.inr ⟨f, hr hf, he⟩)

private theorem joinFacetFaces_surjective {n : ℕ} (d : PolygonDiagonal n) :
    Function.Surjective (joinFacetFaces d) := by
  intro p
  let l : NoncrossingFace (facetLeftArity d) :=
    ⟨Finset.univ.filter (fun e => facetLeftDiagonal d e ∈ p.val.val), by
      intro e he f hf
      exact (facetLeftDiagonal_cross_iff d e f).not.mp
        (p.val.property _ (Finset.mem_filter.mp he).2 _ (Finset.mem_filter.mp hf).2)⟩
  let r : NoncrossingFace (facetRightArity d) :=
    ⟨Finset.univ.filter (fun e => facetRightDiagonal d e ∈ p.val.val), by
      intro e he f hf
      exact (facetRightDiagonal_cross_iff d e f).not.mp
        (p.val.property _ (Finset.mem_filter.mp he).2 _ (Finset.mem_filter.mp hf).2)⟩
  refine ⟨(l, r), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  ext e
  change e ∈ joinFacetDiagonals d (l, r) ↔ e ∈ p.val.val
  rw [mem_joinFacetDiagonals]
  constructor
  · rintro (rfl | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩)
    · exact p.property
    · exact (Finset.mem_filter.mp hf).2
    · exact (Finset.mem_filter.mp hf).2
  · intro he
    by_cases hd : e = d
    · exact Or.inl hd
    · rcases facetDiagonal_sides d e hd (p.val.property d p.property e he) with
        ⟨f, hf⟩ | ⟨f, hf⟩
      · exact Or.inr (Or.inl ⟨f, by simp [l, hf, he], hf⟩)
      · exact Or.inr (Or.inr ⟨f, by simp [r, hf, he], hf⟩)

/-- Every facet has the nonempty face order of a product of two smaller associahedra.
The arities are the endpoint gap and its complementary cyclic length. -/
noncomputable def polygonFacet_product_orderIso {n : ℕ} (d : PolygonDiagonal n) :
    PolygonFacetFaces d ≃o
      NoncrossingFace (facetLeftArity d) × NoncrossingFace (facetRightArity d) :=
  OrderIso.symm
    { toEquiv := Equiv.ofBijective (joinFacetFaces d)
        ⟨by
          intro p q h
          exact le_antisymm ((joinFacetFaces_le_iff d p q).mp (le_of_eq h))
            ((joinFacetFaces_le_iff d q p).mp (le_of_eq h.symm)),
          joinFacetFaces_surjective d⟩
      map_rel_iff' := by intro p q; exact joinFacetFaces_le_iff d p q }

private theorem pointPolygonFace_unique (p : NoncrossingFace 2) : p = wholePolygonFace 2 := by
  apply Subtype.ext
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d _
  have hg := d.gap
  have hb := d.b.isLt
  have hn := d.not_boundary
  omega

private def pointProduct_orderIso (n : ℕ) :
    NoncrossingFace 2 × NoncrossingFace n ≃o NoncrossingFace n where
  toFun := Prod.snd
  invFun p := (wholePolygonFace 2, p)
  left_inv p := by
    apply Prod.ext
    · exact (pointPolygonFace_unique p.1).symm
    · rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro p q
    change p.2 ≤ q.2 ↔ p.1 ≤ q.1 ∧ p.2 ≤ q.2
    rw [pointPolygonFace_unique p.1, pointPolygonFace_unique q.1]
    simp

/-- Shorter boundary distance between the endpoints of a polygon diagonal. -/
def polygonCyclicLength {n : ℕ} (d : PolygonDiagonal n) : ℕ :=
  min (facetLeftArity d) (facetRightArity d)

/-- Every facet of K₅ has the face order of a pentagon or of a square. -/
theorem K5_facet_shape_dichotomy (d : PolygonDiagonal 5) :
    polygonCyclicLength d = 2 ∨ polygonCyclicLength d = 3 := by
  have h := facet_arities d
  dsimp [polygonCyclicLength]
  omega

/-- Cyclic length two cuts a hexagon into a triangle and a pentagon.
Its associahedral facet therefore has the pentagon's nonempty face order. -/
theorem K5_pentagonal_facet (d : PolygonDiagonal 5) (h : polygonCyclicLength d = 2) :
    Nonempty (PolygonFacetFaces d ≃o NoncrossingFace 4) := by
  have hd := facet_arities d
  have hm : facetLeftArity d = 2 ∨ facetLeftArity d = 4 := by
    dsimp [polygonCyclicLength] at h; omega
  rcases hm with hm | hm
  · have hk : facetRightArity d = 4 := by omega
    have iso := polygonFacet_product_orderIso d
    rw [hm, hk] at iso
    exact ⟨iso.trans (pointProduct_orderIso 4)⟩
  · have hk : facetRightArity d = 2 := by omega
    have iso := polygonFacet_product_orderIso d
    rw [hm, hk] at iso
    exact ⟨iso.trans (OrderIso.prodComm.trans (pointProduct_orderIso 4))⟩

/-- Cyclic length three cuts a hexagon into two quadrilaterals.
Its associahedral facet has the face order of the product of two intervals. -/
theorem K5_square_facet (d : PolygonDiagonal 5) (h : polygonCyclicLength d = 3) :
    Nonempty (PolygonFacetFaces d ≃o (NoncrossingFace 3 × NoncrossingFace 3)) := by
  have hd := facet_arities d
  have hm : facetLeftArity d = 3 := by dsimp [polygonCyclicLength] at h; omega
  have hk : facetRightArity d = 3 := by omega
  have iso := polygonFacet_product_orderIso d
  rw [hm, hk] at iso
  exact ⟨iso⟩

/-- A K₅ facet has the pentagon face order exactly when its cyclic length is two. -/
theorem K5_pentagonal_facet_iff (d : PolygonDiagonal 5) :
    Nonempty (PolygonFacetFaces d ≃o NoncrossingFace 4) ↔ polygonCyclicLength d = 2 := by
  constructor
  · rintro ⟨p⟩
    rcases K5_facet_shape_dichotomy d with h | h
    · exact h
    · obtain ⟨q⟩ := K5_square_facet d h
      have hc := Fintype.card_congr (q.symm.trans p).toEquiv
      have h3 : Fintype.card (NoncrossingFace 3) = 3 := K3_face_count
      have h4 : Fintype.card (NoncrossingFace 4) = 11 := K4_face_count
      rw [Fintype.card_prod, h3, h4] at hc
      omega
  · exact K5_pentagonal_facet d

/-- A K₅ facet has the square face order exactly when its cyclic length is three. -/
theorem K5_square_facet_iff (d : PolygonDiagonal 5) :
    Nonempty (PolygonFacetFaces d ≃o (NoncrossingFace 3 × NoncrossingFace 3)) ↔
      polygonCyclicLength d = 3 := by
  constructor
  · rintro ⟨q⟩
    rcases K5_facet_shape_dichotomy d with h | h
    · obtain ⟨p⟩ := K5_pentagonal_facet d h
      have hc := Fintype.card_congr (q.symm.trans p).toEquiv
      have h3 : Fintype.card (NoncrossingFace 3) = 3 := K3_face_count
      have h4 : Fintype.card (NoncrossingFace 4) = 11 := K4_face_count
      rw [Fintype.card_prod, h3, h4] at hc
      omega
    · exact h
  · exact K5_square_facet d

set_option maxRecDepth 4096 in
/-- There are six diagonals indexing pentagonal facets. -/
theorem K5_pentagonal_facet_count :
    Fintype.card {d : PolygonDiagonal 5 // polygonCyclicLength d = 2} = 6 := by decide

set_option maxRecDepth 4096 in
/-- There are three diagonals indexing square facets. -/
theorem K5_square_facet_count :
    Fintype.card {d : PolygonDiagonal 5 // polygonCyclicLength d = 3} = 3 := by decide

/-- Nonempty supporting subfaces of the actual convex facet indexed by `d`. -/
abbrev LodayFacetFaces (n : ℕ) (d : PolygonDiagonal (n + 2)) :=
  {F : LodayExposedFace n // F ≤ polygon_loday_face_orderIso n (singletonPolygonFace d)}

/-- The combinatorial facet interval is the actual supporting-face interval. -/
noncomputable def polygonFacet_loday_subface_orderIso (n : ℕ)
    (d : PolygonDiagonal (n + 2)) : PolygonFacetFaces d ≃o LodayFacetFaces n d where
  toFun p := ⟨polygon_loday_face_orderIso n p.val,
    (polygon_loday_face_orderIso n).monotone ((mem_diagonal_iff_le_facet d p.val).mp p.property)⟩
  invFun F := ⟨(polygon_loday_face_orderIso n).symm F.val, by
    apply (mem_diagonal_iff_le_facet d _).mpr
    simpa using (polygon_loday_face_orderIso n).symm.monotone F.property⟩
  left_inv p := by apply Subtype.ext; exact (polygon_loday_face_orderIso n).symm_apply_apply p.val
  right_inv F := by apply Subtype.ext; exact (polygon_loday_face_orderIso n).apply_symm_apply F.val
  map_rel_iff' := by intro p q; exact (polygon_loday_face_orderIso n).map_rel_iff

/-- The supporting subfaces of every convex facet have the product face order. -/
noncomputable def Loday_facet_product_orderIso (n : ℕ) (d : PolygonDiagonal (n + 2)) :
    LodayFacetFaces n d ≃o
      NoncrossingFace (facetLeftArity d) × NoncrossingFace (facetRightArity d) :=
  (polygonFacet_loday_subface_orderIso n d).symm.trans (polygonFacet_product_orderIso d)

private def productFace_orderIso {A B C D : Type*}
    [PartialOrder A] [PartialOrder B] [PartialOrder C] [PartialOrder D]
    (f : A ≃o B) (g : C ≃o D) : A × C ≃o B × D where
  toEquiv := f.toEquiv.prodCongr g.toEquiv
  map_rel_iff' := by intro p q; exact and_congr f.map_rel_iff g.map_rel_iff

/-- Each actual convex facet has the face order of a product of two smaller
convex associahedra. This asserts combinatorial type, not metric regularity. -/
noncomputable def Loday_facet_geometric_product_orderIso (n : ℕ)
    (d : PolygonDiagonal (n + 2)) :
    LodayFacetFaces n d ≃o
      LodayExposedFace (facetLeftArity d - 2) × LodayExposedFace (facetRightArity d - 2) := by
  have h := facet_arities d
  let l : NoncrossingFace (facetLeftArity d) ≃o LodayExposedFace (facetLeftArity d - 2) := by
    have hl : facetLeftArity d - 2 + 2 = facetLeftArity d := Nat.sub_add_cancel h.1
    have iso := polygon_loday_face_orderIso (facetLeftArity d - 2)
    rw [hl] at iso
    exact iso
  let r : NoncrossingFace (facetRightArity d) ≃o LodayExposedFace (facetRightArity d - 2) := by
    have hr : facetRightArity d - 2 + 2 = facetRightArity d := Nat.sub_add_cancel h.2.1
    have iso := polygon_loday_face_orderIso (facetRightArity d - 2)
    rw [hr] at iso
    exact iso
  exact (Loday_facet_product_orderIso n d).trans (productFace_orderIso l r)

/-- A length-two diagonal indexes an actual pentagonal facet of the 3D realization.
The assertion is about face order, without a claim of metric regularity. -/
theorem Loday_K5_pentagonal_facet (d : PolygonDiagonal 5) (h : polygonCyclicLength d = 2) :
    Nonempty (LodayFacetFaces 3 d ≃o LodayExposedFace 2) := by
  obtain ⟨iso⟩ := K5_pentagonal_facet d h
  exact ⟨(polygonFacet_loday_subface_orderIso 3 d).symm.trans
    (iso.trans (polygon_loday_face_orderIso 2))⟩

/-- A length-three diagonal indexes an actual square facet of the 3D realization.
Its supporting-face order is the product of two interval face orders. -/
theorem Loday_K5_square_facet (d : PolygonDiagonal 5) (h : polygonCyclicLength d = 3) :
    Nonempty (LodayFacetFaces 3 d ≃o (LodayExposedFace 1 × LodayExposedFace 1)) := by
  obtain ⟨iso⟩ := K5_square_facet d h
  exact ⟨(polygonFacet_loday_subface_orderIso 3 d).symm.trans
    (iso.trans (productFace_orderIso (polygon_loday_face_orderIso 1)
      (polygon_loday_face_orderIso 1)))⟩

/-- Actual convex facets, indexed by polygon diagonals through the proved face map. -/
noncomputable def polygonDiagonal_lodayFacet_equiv (n : ℕ) :
    PolygonDiagonal (n + 2) ≃ {F : LodayExposedFace n // IsCoatom F} :=
  (polygonDiagonal_facet_equiv (n + 2)).trans (polygonFacet_lodayFacet_equiv n)

/-- Cyclic length of the diagonal indexing an actual geometric facet of K₅. -/
noncomputable def K5GeometricFacetLength (F : {F : LodayExposedFace 3 // IsCoatom F}) : ℕ :=
  polygonCyclicLength ((polygonDiagonal_lodayFacet_equiv 3).symm F)

noncomputable instance (k : ℕ) :
    Fintype {F : {F : LodayExposedFace 3 // IsCoatom F} // K5GeometricFacetLength F = k} := by
  classical
  infer_instance

/-- Exactly six actual geometric facets have the pentagonal face order. -/
theorem Loday_K5_pentagonal_facet_count :
    Fintype.card {F : {F : LodayExposedFace 3 // IsCoatom F} //
      K5GeometricFacetLength F = 2} = 6 := by
  let e : {d : PolygonDiagonal 5 // polygonCyclicLength d = 2} ≃
      {F : {F : LodayExposedFace 3 // IsCoatom F} // K5GeometricFacetLength F = 2} :=
    (polygonDiagonal_lodayFacet_equiv 3).subtypeEquiv
    (fun d => show polygonCyclicLength d = 2 ↔
      K5GeometricFacetLength (polygonDiagonal_lodayFacet_equiv 3 d) = 2 by
        simp [K5GeometricFacetLength])
  rw [← Fintype.card_congr e, K5_pentagonal_facet_count]

/-- Exactly three actual geometric facets have the square face order. -/
theorem Loday_K5_square_facet_count :
    Fintype.card {F : {F : LodayExposedFace 3 // IsCoatom F} //
      K5GeometricFacetLength F = 3} = 3 := by
  let e : {d : PolygonDiagonal 5 // polygonCyclicLength d = 3} ≃
      {F : {F : LodayExposedFace 3 // IsCoatom F} // K5GeometricFacetLength F = 3} :=
    (polygonDiagonal_lodayFacet_equiv 3).subtypeEquiv
    (fun d => show polygonCyclicLength d = 3 ↔
      K5GeometricFacetLength (polygonDiagonal_lodayFacet_equiv 3 d) = 3 by
        simp [K5GeometricFacetLength])
  rw [← Fintype.card_congr e, K5_square_facet_count]

end FunctorialGeometry
