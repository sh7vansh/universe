/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralSignedDefects
import MathProject.DirectedReassociation

/-! # Geometric dimension and elementary rotation bridges for signed defects -/

namespace FunctorialGeometry

/-- Any partial bracketing extends to a full binary tree. -/
theorem partialBracketing_full_completion {n : ℕ} (hn : 2 ≤ n)
    (p : PartialBracketing n) :
    ∃ t : FullBracketing n, p.val ⊆ (treePartialBracketing t).val := by
  have hs := spanFamily_insert_root hn (properBracketSpans_family p)
  obtain ⟨t, ht, hsub⟩ := spanFamily_complete n (by omega) 0 _ hs
  let t' : FullBracketing n := ⟨t, ht⟩
  refine ⟨t', ?_⟩
  intro b hb
  have hraw : bracketSpan b ∈ treeProperSpans t' := by
    apply Finset.mem_erase.mpr
    constructor
    · exact (properBracketSpans_valid p.val _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)).2
    · exact hsub (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
  rw [← treePartialBracketing_spans] at hraw
  obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hraw
  exact (bracketSpan_injective n he) ▸ hc

/-- Each added compatible bracket decreases actual affine face dimension. -/
theorem Loday_relative_dimension_bound (n : ℕ) (p : PartialBracketing (n + 2))
    (u : Finset (ProperBracket (n + 2))) (hdis : Disjoint p.val u)
    (hu : BracketFamily (p.val ∪ u)) :
    u.card + LodayFaceDimension n (bracketExposedFace n ⟨p.val ∪ u, hu⟩) ≤
      LodayFaceDimension n (bracketExposedFace n p) := by
  induction u using Finset.induction_on with
  | empty =>
    have he : (⟨p.val ∪ ∅, hu⟩ : PartialBracketing (n + 2)) = p :=
      Subtype.ext (Finset.union_empty p.val)
    simpa only [Finset.card_empty, Nat.zero_add, he] using
      le_refl (LodayFaceDimension n (bracketExposedFace n p))
  | @insert a u ha ih =>
    have haP : a ∉ p.val := by
      intro hp
      exact Finset.disjoint_left.mp hdis hp (Finset.mem_insert_self a u)
    have hdis' : Disjoint p.val u := Finset.disjoint_left.mpr (by
      intro b hb hbu
      exact Finset.disjoint_left.mp hdis hb (Finset.mem_insert_of_mem hbu))
    have hsub : p.val ∪ u ⊆ p.val ∪ insert a u := by
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact Finset.mem_union_left _ hb
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hb)
    have hu' := bracketFamily_subset hu hsub
    have hih := ih hdis' hu'
    let q : PartialBracketing (n + 2) := ⟨p.val ∪ insert a u, hu⟩
    let r : PartialBracketing (n + 2) := ⟨p.val ∪ u, hu'⟩
    have hstrict : q < r := by
      change p.val ∪ u ⊂ p.val ∪ insert a u
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub, ?_⟩
      intro he
      have hm : a ∈ p.val ∪ u := he ▸ Finset.mem_union_right p.val
        (Finset.mem_insert_self a u)
      simp [haP, ha] at hm
    have hd := LodayFaceDimension_strict n
      ((partialBracketing_loday_orderIso n).strictMono hstrict)
    change LodayFaceDimension n (bracketExposedFace n q) <
      LodayFaceDimension n (bracketExposedFace n r) at hd
    dsimp [q, r] at hd
    rw [Finset.card_insert_of_notMem ha]
    omega

/-- Every bracket face has its actual geometric dimension, not an assigned dimension. -/
theorem Loday_bracketFace_dimension (n : ℕ) (p : PartialBracketing (n + 2)) :
    LodayFaceDimension n (bracketExposedFace n p) + p.val.card = n := by
  have hupper := Loday_dimension_chain_bound n p.val p.property
  change p.val.card + LodayFaceDimension n (bracketExposedFace n p) ≤
    LodayAffineDimension n at hupper
  rw [Loday_affine_dimension] at hupper
  obtain ⟨t, ht⟩ := partialBracketing_full_completion (by omega : 2 ≤ n + 2) p
  let q := treePartialBracketing t
  have hqcard : q.val.card = n := by
    simpa using treeProperSpans_card (by omega : 2 ≤ n + 2) t
  have hunion : p.val ∪ (q.val \ p.val) = q.val := Finset.union_sdiff_of_subset ht
  have hcompat : BracketFamily (p.val ∪ (q.val \ p.val)) := by
    rw [hunion]
    exact q.property
  have hdis : Disjoint p.val (q.val \ p.val) := Finset.disjoint_left.mpr (by
    intro a ha hmem
    exact (Finset.mem_sdiff.mp hmem).2 ha)
  have hlower := Loday_relative_dimension_bound n p (q.val \ p.val) hdis hcompat
  rw [Finset.card_sdiff_of_subset ht, hqcard] at hlower
  have hpbound : p.val.card ≤ n := by
    simpa using partialBracketing_card_le (by omega : 2 ≤ n + 2) p
  omega

/-- The integer face rank equals actual affine face dimension plus one. -/
theorem completedFaceRank_eq_geometric_dimension (n : ℕ)
    (p : PartialBracketing (n + 2)) :
    completedFaceRank (WithBot.some p) =
      (LodayFaceDimension n (bracketExposedFace n p) : ℤ) + 1 := by
  have h := Loday_bracketFace_dimension n p
  change ((n + 2 : ℕ) : ℤ) - 1 - p.val.card = _
  omega

/-- An elementary right rotation removes exactly one old internal interval. -/
theorem RightRotation.changed_span {s t : BracketTree} (h : RightRotation s t)
    (start : ℕ) :
    ∃ p : BracketSpan, p ∈ treeSpans s start ∧
      (treeSpans s start).erase p ⊆ treeSpans t start ∧ p ∉ treeSpans t start := by
  induction h generalizing start with
  | root a b c =>
    let p : BracketSpan := (start, start + a.numLeaves + b.numLeaves)
    refine ⟨p, ?_, ?_, ?_⟩
    · simp [p, treeSpans]
    · intro q hq
      dsimp [p] at hq
      simp only [treeSpans, BinaryTree.numLeaves, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_union, Nat.add_assoc] at hq ⊢
      aesop
    · intro hp
      have hnew : (start + a.numLeaves,
          start + a.numLeaves + b.numLeaves + c.numLeaves) ∈
          treeSpans (.node () a (.node () b c)) start := by
        simp only [treeSpans, BinaryTree.numLeaves, Finset.mem_insert, Finset.mem_union,
          Nat.add_assoc]
        exact Or.inr (Or.inr (Or.inl trivial))
      have hc := treeSpans_compatible (.node () a (.node () b c)) start _ hp _ hnew
      have ha := a.numLeaves_pos
      have hb := b.numLeaves_pos
      have hc' := c.numLeaves_pos
      dsimp [SpanCompatible, p] at hc
      omega
  | @left s t h u ih =>
    obtain ⟨p, hp, hsub, hnot⟩ := ih start
    have hn := h.numLeaves_eq
    have hv := treeSpans_valid s start p hp
    have hu := u.numLeaves_pos
    refine ⟨p, ?_, ?_, ?_⟩
    · simp only [treeSpans, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inl hp)
    · intro q hq
      have hq' := Finset.mem_erase.mp hq
      simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hq' ⊢
      rcases hq'.2 with hroot | hq | hq
      · left; simpa only [hn] using hroot
      · right; left; exact hsub (Finset.mem_erase.mpr ⟨hq'.1, hq⟩)
      · right; right; simpa only [hn] using hq
    · intro hmem
      simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hmem
      rcases hmem with hroot | hmem | hmem
      · have hp2 := congrArg Prod.snd hroot
        dsimp [SpanValid] at hv
        dsimp at hp2
        omega
      · exact hnot hmem
      · have hw := treeSpans_valid u (start + t.numLeaves) p hmem
        dsimp [SpanValid] at hv hw
        omega
  | @right s t u h ih =>
    obtain ⟨p, hp, hsub, hnot⟩ := ih (start + u.numLeaves)
    have hn := h.numLeaves_eq
    have hv := treeSpans_valid s (start + u.numLeaves) p hp
    have hu := u.numLeaves_pos
    refine ⟨p, ?_, ?_, ?_⟩
    · simp only [treeSpans, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr hp)
    · intro q hq
      have hq' := Finset.mem_erase.mp hq
      simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hq' ⊢
      rcases hq'.2 with hroot | hq | hq
      · left; simpa only [hn] using hroot
      · right; left; exact hq
      · right; right; exact hsub (Finset.mem_erase.mpr ⟨hq'.1, hq⟩)
    · intro hmem
      simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hmem
      rcases hmem with hroot | hmem | hmem
      · have hp1 := congrArg Prod.fst hroot
        dsimp [SpanValid] at hv
        dsimp at hp1
        omega
      · have hw := treeSpans_valid u start p hmem
        dsimp [SpanValid] at hv hw
        omega
      · exact hnot hmem

theorem RightRotation.span_intersection {s t : BracketTree} (h : RightRotation s t)
    (start : ℕ) :
    ∃ p : BracketSpan, p ∈ treeSpans s start ∧ p ∉ treeSpans t start ∧
      treeSpans s start ∩ treeSpans t start = (treeSpans s start).erase p := by
  obtain ⟨p, hp, hsub, hnot⟩ := h.changed_span start
  refine ⟨p, hp, hnot, ?_⟩
  ext q
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨hqs, hqt⟩
    exact ⟨fun he => hnot (he ▸ hqt), hqs⟩
  · rintro ⟨hne, hqs⟩
    exact ⟨hqs, hsub (Finset.mem_erase.mpr ⟨hne, hqs⟩)⟩

/-- Adjacent full bracketings share precisely all but one proper bracket. -/
theorem RightRotation.proper_bracket_intersection_card {n : ℕ} (hn : 2 ≤ n)
    (s t : FullBracketing n) (h : RightRotation s.val t.val) :
    ((treePartialBracketing s).val ∩ (treePartialBracketing t).val).card = n - 3 := by
  obtain ⟨p, hp, hnot, hinter⟩ := h.span_intersection 0
  have hpRoot : p ≠ (0, n) := by
    intro he
    apply hnot
    rw [he]
    simpa only [Nat.zero_add, t.property] using
      treeSpans_root 0 (by simpa only [t.property] using hn : 2 ≤ t.val.numLeaves)
  have hpProper : p ∈ treeProperSpans s := Finset.mem_erase.mpr ⟨hpRoot, hp⟩
  have hproperInter : treeProperSpans s ∩ treeProperSpans t = (treeProperSpans s).erase p := by
    ext q
    have hi := Finset.ext_iff.mp hinter q
    simp only [Finset.mem_inter, Finset.mem_erase] at hi
    simp only [treeProperSpans, Finset.mem_inter, Finset.mem_erase]
    tauto
  have hmapInter : properBracketSpans
      ((treePartialBracketing s).val ∩ (treePartialBracketing t).val) =
      treeProperSpans s ∩ treeProperSpans t := by
    rw [properBracketSpans, Finset.image_inter _ _ (bracketSpan_injective n)]
    change properBracketSpans (treePartialBracketing s).val ∩
      properBracketSpans (treePartialBracketing t).val = _
    rw [treePartialBracketing_spans, treePartialBracketing_spans]
  have hc := congrArg Finset.card (hmapInter.trans hproperInter)
  rw [properBracketSpans_card, Finset.card_erase_of_mem hpProper] at hc
  have hcard : (treeProperSpans s).card = n - 2 := by
    rw [← treePartialBracketing_spans, properBracketSpans_card]
    exact treeProperSpans_card hn s
  rw [hcard] at hc
  omega

theorem RightRotation.fullBracketings_ne {n : ℕ}
    (s t : FullBracketing n) (h : RightRotation s.val t.val) : s ≠ t := by
  obtain ⟨p, hp, hnot, _⟩ := h.span_intersection 0
  intro he
  exact hnot (he ▸ hp)

/-- Elementary reassociation has zero signed face defect in either direction. -/
theorem rightRotation_signedFaceDefect_zero {n : ℕ} (hn : 2 ≤ n)
    (s t : FullBracketing n) (h : RightRotation s.val t.val) :
    signedFaceDefect (WithBot.some (treePartialBracketing s))
      (WithBot.some (treePartialBracketing t)) = 0 := by
  rw [signedFaceDefect_fullBracketings hn s t (h.fullBracketings_ne s t),
    h.proper_bracket_intersection_card hn s t]
  have hn3 : 3 ≤ n := by
    simpa only [s.property] using h.numLeaves_ge_three
  omega

theorem rotationStep_signedFaceDefect_zero {n : ℕ} (hn : 2 ≤ n)
    (s t : FullBracketing n) (e : RotationStep s.val t.val) :
    signedFaceDefect (WithBot.some (treePartialBracketing s))
      (WithBot.some (treePartialBracketing t)) = 0 := by
  cases e with
  | right h => exact rightRotation_signedFaceDefect_zero hn s t h
  | left h =>
    rw [signedFaceDefect, modularityDefect_comm]
    exact rightRotation_signedFaceDefect_zero hn t s h

/-- The common face of the rotated vertices is an actual geometric edge. -/
theorem rightRotation_commonFace_dimension (n : ℕ) (s t : FullBracketing (n + 2))
    (h : RightRotation s.val t.val) :
    LodayFaceDimension n (bracketExposedFace n
      (bracketIntersection (treePartialBracketing s) (treePartialBracketing t))) = 1 := by
  have hc := h.proper_bracket_intersection_card (by omega : 2 ≤ n + 2) s t
  have hd := Loday_bracketFace_dimension n
    (bracketIntersection (treePartialBracketing s) (treePartialBracketing t))
  change LodayFaceDimension n (bracketExposedFace n
      (bracketIntersection (treePartialBracketing s) (treePartialBracketing t))) +
    ((treePartialBracketing s).val ∩ (treePartialBracketing t).val).card = n at hd
  have hn := h.numLeaves_ge_three
  rw [s.property] at hn
  omega

end FunctorialGeometry
