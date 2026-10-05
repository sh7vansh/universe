/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralComposition
import Mathlib.Data.Finset.Max

/-! # Binary trees and maximal compatible interval families -/

namespace FunctorialGeometry

abbrev BracketSpan := ℕ × ℕ

/-- A group of at least two inputs, allowing the whole word. -/
def SpanValid (start length : ℕ) (p : BracketSpan) : Prop :=
  start ≤ p.1 ∧ p.1 + 2 ≤ p.2 ∧ p.2 ≤ start + length

/-- Disjoint or nested half-open intervals. -/
def SpanCompatible (p q : BracketSpan) : Prop :=
  p.2 ≤ q.1 ∨ q.2 ≤ p.1 ∨
  (p.1 ≤ q.1 ∧ q.2 ≤ p.2) ∨ (q.1 ≤ p.1 ∧ p.2 ≤ q.2)

def SpanFamily (start length : ℕ) (s : Finset BracketSpan) : Prop :=
  (∀ p ∈ s, SpanValid start length p) ∧
  (∀ p ∈ s, ∀ q ∈ s, SpanCompatible p q)

/-- All internal-node intervals, including the root interval. -/
def treeSpans : BinaryTree Unit → ℕ → Finset BracketSpan
  | .nil, _ => ∅
  | .node _ l r, start =>
    insert (start, start + l.numLeaves + r.numLeaves)
      (treeSpans l start ∪ treeSpans r (start + l.numLeaves))

theorem treeSpans_valid (t : BinaryTree Unit) (start : ℕ) :
    ∀ p ∈ treeSpans t start, SpanValid start t.numLeaves p := by
  induction t generalizing start with
  | nil => simp [treeSpans]
  | node _ l r il ir =>
    intro p hp
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with rfl | hp | hp
    · dsimp [SpanValid]; omega
    · have h := il start p hp
      dsimp [SpanValid] at h ⊢
      omega
    · have h := ir (start + l.numLeaves) p hp
      dsimp [SpanValid] at h ⊢
      omega

theorem treeSpans_compatible (t : BinaryTree Unit) (start : ℕ) :
    ∀ p ∈ treeSpans t start, ∀ q ∈ treeSpans t start, SpanCompatible p q := by
  induction t generalizing start with
  | nil => simp [treeSpans]
  | node _ l r il ir =>
    intro p hp q hq
    have hlp := treeSpans_valid l start
    have hrp := treeSpans_valid r (start + l.numLeaves)
    have vp := treeSpans_valid (.node () l r) start p hp
    have vq := treeSpans_valid (.node () l r) start q hq
    simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hp hq
    dsimp [SpanValid] at vp vq
    rcases hp with rfl | hp | hp <;> rcases hq with rfl | hq | hq
    · simp [SpanCompatible]
    · dsimp [SpanCompatible]; omega
    · dsimp [SpanCompatible]; omega
    · dsimp [SpanCompatible]; omega
    · exact il start _ hp _ hq
    · have hp' := hlp _ hp; have hq' := hrp _ hq
      dsimp [SpanValid, SpanCompatible] at *; omega
    · dsimp [SpanCompatible]; omega
    · have hp' := hrp _ hp; have hq' := hlp _ hq
      dsimp [SpanValid, SpanCompatible] at *; omega
    · exact ir (start + l.numLeaves) _ hp _ hq

theorem treeSpans_family (t : BinaryTree Unit) (start : ℕ) :
    SpanFamily start t.numLeaves (treeSpans t start) :=
  ⟨treeSpans_valid t start, treeSpans_compatible t start⟩

theorem treeSpans_card (t : BinaryTree Unit) (start : ℕ) :
    (treeSpans t start).card = t.numNodes := by
  induction t generalizing start with
  | nil => rfl
  | node _ l r il ir =>
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    have hn : (start, start + l.numLeaves + r.numLeaves) ∉
        treeSpans l start ∪ treeSpans r (start + l.numLeaves) := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · have h := treeSpans_valid l start _ h
        dsimp [SpanValid] at h; omega
      · have h := treeSpans_valid r (start + l.numLeaves) _ h
        dsimp [SpanValid] at h; omega
    have hd : Disjoint (treeSpans l start) (treeSpans r (start + l.numLeaves)) := by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      have hp := treeSpans_valid l start p hp
      have hq := treeSpans_valid r (start + l.numLeaves) p hq
      dsimp [SpanValid] at *; omega
    simp only [treeSpans, Finset.card_insert_of_notMem hn, Finset.card_union_of_disjoint hd,
      il, ir, BinaryTree.numNodes]

/-- Every laminar interval family can be completed to a binary tree. -/
theorem spanFamily_complete (length : ℕ) (hpos : 0 < length) (start : ℕ)
    (s : Finset BracketSpan) (hs : SpanFamily start length s) :
    ∃ t : BinaryTree Unit, t.numLeaves = length ∧ s ⊆ treeSpans t start := by
  induction length using Nat.strong_induction_on generalizing start s with
  | h length ih =>
    by_cases h1 : length = 1
    · refine ⟨.nil, h1.symm, ?_⟩
      intro p hp
      have h := hs.1 p hp
      dsimp [SpanValid] at h
      omega
    · let prefixSet := s.filter (fun p => p.1 = start ∧ p.2 < start + length)
      let cut := max (start + 1) (prefixSet.sup Prod.snd)
      have hcut_lo : start < cut := by dsimp [cut]; omega
      have hprefixSet_bound : prefixSet.sup Prod.snd < start + length := by
        have hb : prefixSet.sup Prod.snd ≤ start + length - 1 := by
          apply Finset.sup_le
          intro p hp
          have h := (Finset.mem_filter.mp hp).2.2
          omega
        omega
      have hcut_hi : cut < start + length := by dsimp [cut]; omega
      have hprefixSet_le : ∀ p ∈ prefixSet, p.2 ≤ cut := by
        intro p hp
        exact le_trans (Finset.le_sup (f := Prod.snd) hp) (le_max_right _ _)
      have hsplit : ∀ p ∈ s, p = (start, start + length) ∨ p.2 ≤ cut ∨ cut ≤ p.1 := by
        intro p hp
        have hv := hs.1 p hp
        by_cases hl : p.2 ≤ cut
        · exact Or.inr (Or.inl hl)
        by_cases hr : cut ≤ p.1
        · exact Or.inr (Or.inr hr)
        have hp_start : p.1 = start := by
          by_cases hc : cut = start + 1
          · dsimp [SpanValid] at hv; omega
          · have hsup : prefixSet.sup Prod.snd = cut := by dsimp [cut] at *; omega
            have hne : prefixSet.Nonempty := by
              by_contra h
              have he : prefixSet = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
              simp [he] at hsup
              omega
            obtain ⟨q, hq, heq⟩ := Finset.exists_mem_eq_sup prefixSet hne Prod.snd
            have hq' := Finset.mem_filter.mp hq
            have hcompat := hs.2 p hp q hq'.1
            dsimp [SpanValid, SpanCompatible] at *
            omega
        by_cases he : p.2 = start + length
        · exact Or.inl (Prod.ext hp_start he)
        · have hmem : p ∈ prefixSet := Finset.mem_filter.mpr ⟨hp, hp_start, by
            dsimp [SpanValid] at hv; omega⟩
          have hle := hprefixSet_le p hmem
          omega
      let sl := s.filter (fun p => p.2 ≤ cut)
      let sr := s.filter (fun p => cut ≤ p.1)
      have hsl : SpanFamily start (cut - start) sl := by
        constructor
        · intro p hp
          have hp' := Finset.mem_filter.mp hp
          have hv := hs.1 p hp'.1
          dsimp [SpanValid] at hv ⊢; omega
        · intro p hp q hq
          exact hs.2 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      have hsr : SpanFamily cut (start + length - cut) sr := by
        constructor
        · intro p hp
          have hp' := Finset.mem_filter.mp hp
          have hv := hs.1 p hp'.1
          dsimp [SpanValid] at hv ⊢; omega
        · intro p hp q hq
          exact hs.2 p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      obtain ⟨l, hl, hls⟩ := ih (cut - start) (by omega) (by omega) start sl hsl
      obtain ⟨r, hr, hrs⟩ := ih (start + length - cut) (by omega) (by omega) cut sr hsr
      refine ⟨.node () l r, by simp only [BinaryTree.numLeaves, hl, hr]; omega, ?_⟩
      intro p hp
      simp only [treeSpans, Finset.mem_insert, Finset.mem_union, hl, hr]
      rcases hsplit p hp with he | hle | hge
      · left; rw [he]; congr 1; omega
      · right; left; exact hls (Finset.mem_filter.mpr ⟨hp, hle⟩)
      · right; right
        have ha : start + (cut - start) = cut := by omega
        rw [ha]
        exact hrs (Finset.mem_filter.mpr ⟨hp, hge⟩)

/-- A laminar family on `n` inputs has at most `n - 1` internal groups. -/
theorem spanFamily_card_le {start length : ℕ} (hpos : 0 < length)
    {s : Finset BracketSpan} (hs : SpanFamily start length s) : s.card ≤ length - 1 := by
  obtain ⟨t, ht, hsub⟩ := spanFamily_complete length hpos start s hs
  have hc := Finset.card_le_card hsub
  rw [treeSpans_card] at hc
  have hn := t.numLeaves_eq_numNodes_succ
  omega

theorem treeSpans_root {t : BinaryTree Unit} (start : ℕ) (h : 2 ≤ t.numLeaves) :
    (start, start + t.numLeaves) ∈ treeSpans t start := by
  cases t with
  | nil => simp at h
  | node _ l r => simp [treeSpans, Nat.add_assoc]

private theorem treeSpans_prefix_le (l r : BinaryTree Unit) (start : ℕ)
    (p : BracketSpan) (hp : p ∈ treeSpans (.node () l r) start)
    (hstart : p.1 = start) (hproper : p.2 < start + l.numLeaves + r.numLeaves) :
    p.2 ≤ start + l.numLeaves := by
  have hl := l.numLeaves_pos
  simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hp
  rcases hp with rfl | hp | hp
  · omega
  · exact (treeSpans_valid l start p hp).2.2
  · have h := treeSpans_valid r (start + l.numLeaves) p hp
    dsimp [SpanValid] at h; omega

private theorem treeSpans_filter_left (l r : BinaryTree Unit) (start : ℕ) :
    (treeSpans (.node () l r) start).filter (fun p => p.2 ≤ start + l.numLeaves) =
      treeSpans l start := by
  ext p
  simp only [Finset.mem_filter, treeSpans, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨hp, hbound⟩
    rcases hp with rfl | hp | hp
    · have h := r.numLeaves_pos; omega
    · exact hp
    · have h := treeSpans_valid r (start + l.numLeaves) p hp
      dsimp [SpanValid] at h; omega
  · intro hp
    exact ⟨Or.inr (Or.inl hp), (treeSpans_valid l start p hp).2.2⟩

private theorem treeSpans_filter_right (l r : BinaryTree Unit) (start : ℕ) :
    (treeSpans (.node () l r) start).filter (fun p => start + l.numLeaves ≤ p.1) =
      treeSpans r (start + l.numLeaves) := by
  ext p
  simp only [Finset.mem_filter, treeSpans, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨hp, hbound⟩
    rcases hp with rfl | hp | hp
    · have h := l.numLeaves_pos; omega
    · have h := treeSpans_valid l start p hp
      dsimp [SpanValid] at h; omega
    · exact hp
  · intro hp
    exact ⟨Or.inr (Or.inr hp), (treeSpans_valid r (start + l.numLeaves) p hp).1⟩

/-- The internal intervals recover the entire binary tree. -/
theorem treeSpans_injective (t u : BinaryTree Unit) (start : ℕ)
    (hleaves : t.numLeaves = u.numLeaves)
    (hspans : treeSpans t start = treeSpans u start) : t = u := by
  induction t generalizing u start with
  | nil =>
    cases u with
    | nil => rfl
    | node _ l r =>
      have hl := l.numLeaves_pos; have hr := r.numLeaves_pos
      simp only [BinaryTree.numLeaves] at hleaves
      omega
  | node val l r il ir =>
    cases val
    cases u with
    | nil =>
      have hl := l.numLeaves_pos; have hr := r.numLeaves_pos
      simp only [BinaryTree.numLeaves] at hleaves
      omega
    | node val' l' r' =>
      cases val'
      have hl := l.numLeaves_pos; have hr := r.numLeaves_pos
      have hl' := l'.numLeaves_pos; have hr' := r'.numLeaves_pos
      simp only [BinaryTree.numLeaves] at hleaves
      have compare : ∀ a b c d : BinaryTree Unit,
          a.numLeaves + b.numLeaves = c.numLeaves + d.numLeaves →
          treeSpans (.node () a b) start = treeSpans (.node () c d) start →
          a.numLeaves ≤ c.numLeaves := by
        intro a b c d hn hs
        have ha := a.numLeaves_pos; have hb := b.numLeaves_pos
        have hc := c.numLeaves_pos; have hd := d.numLeaves_pos
        by_cases ha1 : a.numLeaves = 1
        · omega
        · have hmem : (start, start + a.numLeaves) ∈ treeSpans (.node () a b) start := by
            simp only [treeSpans, Finset.mem_insert, Finset.mem_union]
            exact Or.inr (Or.inl (treeSpans_root start (by omega)))
          rw [hs] at hmem
          have hbound := treeSpans_prefix_le c d start _ hmem rfl (by omega)
          omega
      have hleft : l.numLeaves = l'.numLeaves :=
        Nat.le_antisymm (compare l r l' r' hleaves hspans)
          (compare l' r' l r hleaves.symm hspans.symm)
      have hright : r.numLeaves = r'.numLeaves := by omega
      have hls := congrArg (Finset.filter (fun p : BracketSpan => p.2 ≤ start + l.numLeaves)) hspans
      rw [treeSpans_filter_left, hleft, treeSpans_filter_left] at hls
      have hrs := congrArg (Finset.filter (fun p : BracketSpan => start + l.numLeaves ≤ p.1)) hspans
      rw [treeSpans_filter_right, hleft, treeSpans_filter_right] at hrs
      have el : l = l' := il l' start hleft hls
      have er : r = r' := ir r' (start + l'.numLeaves) hright hrs
      rw [el, er]

/-- Tree interval families are maximal among compatible interval families. -/
theorem treeSpans_maximal (t : BinaryTree Unit) (start : ℕ)
    {s : Finset BracketSpan} (hs : SpanFamily start t.numLeaves s)
    (hsub : treeSpans t start ⊆ s) : s = treeSpans t start := by
  apply (Finset.eq_of_subset_of_card_le hsub _).symm
  have h := spanFamily_card_le t.numLeaves_pos hs
  rw [treeSpans_card]
  have hn := t.numLeaves_eq_numNodes_succ
  omega

/-- Forget the bounded endpoint types of a proper bracket. -/
def bracketSpan {n : ℕ} (p : ProperBracket n) : BracketSpan := (p.left.val, p.right.val)

theorem bracketSpan_injective (n : ℕ) : Function.Injective (@bracketSpan n) := by
  intro p q h
  apply ProperBracket.ext
  · exact Fin.ext (congrArg Prod.fst h)
  · exact Fin.ext (congrArg Prod.snd h)

def properBracketSpans {n : ℕ} (s : Finset (ProperBracket n)) : Finset BracketSpan :=
  s.image bracketSpan

theorem properBracketSpans_injective (n : ℕ) :
    Function.Injective (@properBracketSpans n) :=
  Finset.image_injective (bracketSpan_injective n)

theorem properBracketSpans_card {n : ℕ} (s : Finset (ProperBracket n)) :
    (properBracketSpans s).card = s.card :=
  Finset.card_image_of_injective s (bracketSpan_injective n)

def spanToBracket {n : ℕ} (p : BracketSpan)
    (h : SpanValid 0 n p ∧ p ≠ (0, n)) : ProperBracket n where
  left := ⟨p.1, by have hv := h.1; dsimp [SpanValid] at hv; omega⟩
  right := ⟨p.2, by have hv := h.1; dsimp [SpanValid] at hv; omega⟩
  length_two := h.1.2.1
  proper := by
    intro he
    apply h.2
    exact Prod.ext he.1 he.2

def spansToBrackets (n : ℕ) (s : Finset BracketSpan)
    (hs : ∀ p ∈ s, SpanValid 0 n p ∧ p ≠ (0, n)) : Finset (ProperBracket n) :=
  s.attach.image fun p => spanToBracket p.val (hs p.val p.property)

theorem properBracketSpans_spansToBrackets (n : ℕ) (s : Finset BracketSpan)
    (hs : ∀ p ∈ s, SpanValid 0 n p ∧ p ≠ (0, n)) :
    properBracketSpans (spansToBrackets n s hs) = s := by
  unfold properBracketSpans spansToBrackets
  rw [Finset.image_image]
  change s.attach.image Subtype.val = s
  exact Finset.attach_image_val

theorem properBracketSpans_valid {n : ℕ} (s : Finset (ProperBracket n)) :
    ∀ p ∈ properBracketSpans s, SpanValid 0 n p ∧ p ≠ (0, n) := by
  intro p hp
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hp
  constructor
  · have hb := b.right.isLt
    have hl := b.length_two
    dsimp [SpanValid, bracketSpan]; omega
  · intro h
    exact b.proper ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem properBracketSpans_family {n : ℕ} (p : PartialBracketing n) :
    SpanFamily 0 n (properBracketSpans p.val) := by
  constructor
  · intro b hb; exact (properBracketSpans_valid p.val b hb).1
  · intro b hb c hc
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    exact p.property b' hb' c' hc'

theorem spanFamily_insert_root {n : ℕ} (hn : 2 ≤ n) {s : Finset BracketSpan}
    (hs : SpanFamily 0 n s) : SpanFamily 0 n (insert (0, n) s) := by
  constructor
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · dsimp [SpanValid]; omega
    · exact hs.1 p hp
  · intro p hp q hq
    rcases Finset.mem_insert.mp hp with rfl | hp <;>
      rcases Finset.mem_insert.mp hq with rfl | hq
    · simp [SpanCompatible]
    · have h := hs.1 q hq; dsimp [SpanCompatible, SpanValid] at *; omega
    · have h := hs.1 p hp; dsimp [SpanCompatible, SpanValid] at *; omega
    · exact hs.2 p hp q hq

def treeProperSpans {n : ℕ} (t : FullBracketing n) : Finset BracketSpan :=
  (treeSpans t.val 0).erase (0, n)

theorem treeProperSpans_valid {n : ℕ} (t : FullBracketing n) :
    ∀ p ∈ treeProperSpans t, SpanValid 0 n p ∧ p ≠ (0, n) := by
  intro p hp
  have he := Finset.mem_erase.mp hp
  have hv := treeSpans_valid t.val 0 p he.2
  rw [t.property] at hv
  exact ⟨hv, he.1⟩

/-- The proper internal-node intervals of a full binary bracketing. -/
def treePartialBracketing {n : ℕ} (t : FullBracketing n) : PartialBracketing n :=
  ⟨spansToBrackets n (treeProperSpans t) (treeProperSpans_valid t), by
    intro p hp q hq
    have he := properBracketSpans_spansToBrackets n (treeProperSpans t) (treeProperSpans_valid t)
    have hp' : bracketSpan p ∈ treeProperSpans t := by
      rw [← he]; exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hq' : bracketSpan q ∈ treeProperSpans t := by
      rw [← he]; exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    exact treeSpans_compatible t.val 0 _ (Finset.mem_erase.mp hp').2
      _ (Finset.mem_erase.mp hq').2⟩

@[simp] theorem treePartialBracketing_spans {n : ℕ} (t : FullBracketing n) :
    properBracketSpans (treePartialBracketing t).val = treeProperSpans t :=
  properBracketSpans_spansToBrackets n (treeProperSpans t) (treeProperSpans_valid t)

theorem treeProperSpans_restore {n : ℕ} (hn : 2 ≤ n) (t : FullBracketing n) :
    insert (0, n) (treeProperSpans t) = treeSpans t.val 0 := by
  apply Finset.insert_erase
  simpa only [Nat.zero_add, t.property] using
    treeSpans_root 0 (by simpa only [t.property] using hn : 2 ≤ t.val.numLeaves)

theorem treeProperSpans_card {n : ℕ} (hn : 2 ≤ n) (t : FullBracketing n) :
    (treePartialBracketing t).val.card = n - 2 := by
  have hr := treeProperSpans_restore hn t
  have hc := congrArg Finset.card hr
  have hnot : (0, n) ∉ treeProperSpans t := Finset.notMem_erase _ _
  rw [Finset.card_insert_of_notMem hnot, treeSpans_card] at hc
  have hmap := properBracketSpans_card (treePartialBracketing t).val
  rw [treePartialBracketing_spans] at hmap
  have hn' := t.val.numLeaves_eq_numNodes_succ
  rw [t.property] at hn'
  omega

/-- Minimal nonempty faces are vertices, in the reverse-inclusion face order. -/
def IsBracketVertex {n : ℕ} (p : PartialBracketing n) : Prop :=
  ∀ q : PartialBracketing n, q ≤ p → q = p

def IsPolygonVertex {n : ℕ} (p : NoncrossingFace n) : Prop :=
  ∀ q : NoncrossingFace n, q ≤ p → q = p

theorem bracketVertex_iff_polygonVertex {n : ℕ} (p : PartialBracketing n) :
    IsBracketVertex p ↔ IsPolygonVertex (partialBracketing_face_orderIso n p) := by
  constructor
  · intro h q hq
    have hq' : (partialBracketing_face_orderIso n).symm q ≤ p := by
      simpa using (partialBracketing_face_orderIso n).symm.monotone hq
    have he := h _ hq'
    simpa using congrArg (partialBracketing_face_orderIso n) he
  · intro h q hq
    have he := h _ ((partialBracketing_face_orderIso n).monotone hq)
    exact (partialBracketing_face_orderIso n).injective he

theorem treePartialBracketing_vertex {n : ℕ} (hn : 2 ≤ n) (t : FullBracketing n) :
    IsBracketVertex (treePartialBracketing t) := by
  intro q hq
  have hs := spanFamily_insert_root hn (properBracketSpans_family q)
  have hsub : treeSpans t.val 0 ⊆ insert (0, n) (properBracketSpans q.val) := by
    rw [← treeProperSpans_restore hn t]
    apply Finset.insert_subset_insert
    rw [← treePartialBracketing_spans]
    exact Finset.image_subset_image hq
  have hs' : SpanFamily 0 t.val.numLeaves (insert (0, n) (properBracketSpans q.val)) := by
    simpa only [t.property] using hs
  have he := treeSpans_maximal t.val 0 hs' hsub
  have he' := congrArg (fun s => s.erase (0, n)) he
  have hnot : (0, n) ∉ properBracketSpans q.val := by
    intro h; exact (properBracketSpans_valid q.val _ h).2 rfl
  rw [Finset.erase_insert hnot] at he'
  apply Subtype.ext
  apply properBracketSpans_injective n
  rw [treePartialBracketing_spans]
  exact he'

theorem bracketVertex_is_tree {n : ℕ} (hn : 2 ≤ n) (p : PartialBracketing n)
    (hp : IsBracketVertex p) : ∃ t : FullBracketing n, treePartialBracketing t = p := by
  have hs := spanFamily_insert_root hn (properBracketSpans_family p)
  obtain ⟨t, ht, hsub⟩ := spanFamily_complete n (by omega) 0 _ hs
  let t' : FullBracketing n := ⟨t, ht⟩
  refine ⟨t', hp (treePartialBracketing t') ?_⟩
  change p.val ⊆ (treePartialBracketing t').val
  intro b hb
  have hraw : bracketSpan b ∈ treeProperSpans t' := by
    apply Finset.mem_erase.mpr
    constructor
    · exact (properBracketSpans_valid p.val _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)).2
    · exact hsub (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
  rw [← treePartialBracketing_spans] at hraw
  obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hraw
  have he' : c = b := bracketSpan_injective n he
  exact he' ▸ hc

theorem treePartialBracketing_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (@treePartialBracketing n) := by
  intro t u he
  apply Subtype.ext
  apply treeSpans_injective t.val u.val 0 (t.property.trans u.property.symm)
  have he' := congrArg (fun p : PartialBracketing n => properBracketSpans p.val) he
  rw [treePartialBracketing_spans, treePartialBracketing_spans] at he'
  rw [← treeProperSpans_restore hn t, ← treeProperSpans_restore hn u, he']

/-- Full binary bracketings classify the vertices of the polygon face model. -/
noncomputable def fullBracketing_vertex_equiv (n : ℕ) (hn : 2 ≤ n) :
    FullBracketing n ≃ {p : NoncrossingFace n // IsPolygonVertex p} := by
  let f : FullBracketing n → {p : NoncrossingFace n // IsPolygonVertex p} := fun t =>
    ⟨partialBracketing_face_orderIso n (treePartialBracketing t),
      (bracketVertex_iff_polygonVertex _).mp (treePartialBracketing_vertex hn t)⟩
  apply Equiv.ofBijective f
  constructor
  · intro t u he
    apply treePartialBracketing_injective hn
    exact (partialBracketing_face_orderIso n).injective (congrArg Subtype.val he)
  · intro p
    let q := (partialBracketing_face_orderIso n).symm p.val
    have hq : IsBracketVertex q := by
      apply (bracketVertex_iff_polygonVertex q).mpr
      simpa [q] using p.property
    obtain ⟨t, ht⟩ := bracketVertex_is_tree hn q hq
    refine ⟨t, ?_⟩
    apply Subtype.ext
    change partialBracketing_face_orderIso n (treePartialBracketing t) = p.val
    rw [ht]
    exact (partialBracketing_face_orderIso n).apply_symm_apply p.val

/-- Every proper compatible bracket family has at most `n - 2` groups. -/
theorem partialBracketing_card_le {n : ℕ} (hn : 2 ≤ n) (p : PartialBracketing n) :
    p.val.card ≤ n - 2 := by
  have hs := spanFamily_insert_root hn (properBracketSpans_family p)
  have h := spanFamily_card_le (by omega : 0 < n) hs
  have hnot : (0, n) ∉ properBracketSpans p.val := by
    intro h; exact (properBracketSpans_valid p.val _ h).2 rfl
  rw [Finset.card_insert_of_notMem hnot, properBracketSpans_card] at h
  omega

noncomputable instance (n : ℕ) : Fintype {p : NoncrossingFace n // IsPolygonVertex p} := by
  classical
  infer_instance

/-- The Catalan formula now counts actual minimal faces of the polygon face order. -/
theorem polygon_vertex_count (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card {p : NoncrossingFace (m + 1) // IsPolygonVertex p} = catalan m := by
  rw [← Fintype.card_congr (fullBracketing_vertex_equiv (m + 1) (by omega)),
    fullBracketing_card]

theorem polygon_vertex_count_formula (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card {p : NoncrossingFace (m + 1) // IsPolygonVertex p} =
      Nat.choose (2 * m) m / (m + 1) := by
  rw [polygon_vertex_count m hm, catalan_eq_centralBinom_div]
  rfl

theorem noncrossingFace_card_le {n : ℕ} (hn : 2 ≤ n) (p : NoncrossingFace n) :
    p.val.card ≤ n - 2 := by
  let q := (partialBracketing_face_orderIso n).symm p
  have h := partialBracketing_card_le hn q
  have he : partialBracketing_face_orderIso n q = p :=
    (partialBracketing_face_orderIso n).apply_symm_apply p
  have hc : (partialBracketing_face_orderIso n q).val.card = q.val.card :=
    Finset.card_map _
  rw [he] at hc
  omega

theorem polygonVertex_card {n : ℕ} (hn : 2 ≤ n) (p : NoncrossingFace n)
    (hp : IsPolygonVertex p) : p.val.card = n - 2 := by
  let q := (partialBracketing_face_orderIso n).symm p
  have hq : IsBracketVertex q := by
    apply (bracketVertex_iff_polygonVertex q).mpr
    simpa [q] using hp
  obtain ⟨t, ht⟩ := bracketVertex_is_tree hn q hq
  have hc := treeProperSpans_card hn t
  rw [ht] at hc
  have he : partialBracketing_face_orderIso n q = p :=
    (partialBracketing_face_orderIso n).apply_symm_apply p
  have hmap : (partialBracketing_face_orderIso n q).val.card = q.val.card :=
    Finset.card_map _
  rw [he] at hmap
  exact hmap.trans hc

/-- A canonical full bracketing with `m + 1` inputs. -/
def rightComb : ℕ → BinaryTree Unit
  | 0 => .nil
  | m + 1 => .node () .nil (rightComb m)

@[simp] theorem rightComb_leaves (m : ℕ) : (rightComb m).numLeaves = m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [rightComb, ih, Nat.add_comm]

/-- Maximum codimension in the nonempty face order; the combinatorial dimension. -/
def KnCombinatorialDimension (n : ℕ) : ℕ :=
  Finset.univ.sup (fun p : NoncrossingFace n => p.val.card)

/-- The general dimension formula for the combinatorial associahedron. -/
theorem Kn_combinatorial_dimension (n : ℕ) (hn : 2 ≤ n) :
    KnCombinatorialDimension n = n - 2 := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro p _
    exact noncrossingFace_card_le hn p
  · let t : FullBracketing n := ⟨rightComb (n - 1), by simp; omega⟩
    let p := partialBracketing_face_orderIso n (treePartialBracketing t)
    have hp : IsPolygonVertex p :=
      (bracketVertex_iff_polygonVertex _).mp (treePartialBracketing_vertex hn t)
    have h := Finset.le_sup (f := fun q : NoncrossingFace n => q.val.card) (Finset.mem_univ p)
    rw [polygonVertex_card hn p hp] at h
    exact h

/-- The empty diagonal set is the whole face. -/
def wholePolygonFace (n : ℕ) : NoncrossingFace n := ⟨∅, by simp⟩

/-- A facet is a maximal proper face, defined from the face order. -/
def IsPolygonFacet {n : ℕ} (p : NoncrossingFace n) : Prop :=
  p.val.Nonempty ∧ ∀ q : NoncrossingFace n, p ≤ q → q = p ∨ q.val = ∅

def singletonPolygonFace {n : ℕ} (d : PolygonDiagonal n) : NoncrossingFace n :=
  ⟨{d}, by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a b
    simp [DiagonalsCross]⟩

/-- Facets correspond to single diagonals, as a theorem about the face order. -/
theorem polygonFacet_iff_card_one {n : ℕ} (p : NoncrossingFace n) :
    IsPolygonFacet p ↔ p.val.card = 1 := by
  constructor
  · rintro ⟨hne, hmax⟩
    obtain ⟨d, hd⟩ := hne
    have hle : p ≤ singletonPolygonFace d := Finset.singleton_subset_iff.mpr hd
    rcases hmax _ hle with he | he
    · have hs := congrArg Subtype.val he
      rw [← hs]
      exact Finset.card_singleton d
    · exact False.elim (Finset.singleton_ne_empty d he)
  · intro hc
    obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hc
    constructor
    · rw [hd]; exact Finset.singleton_nonempty d
    · intro q hq
      have hsub : q.val ⊆ {d} := hd ▸ hq
      rcases Finset.subset_singleton_iff.mp hsub with he | he
      · exact Or.inr he
      · left; apply Subtype.ext; exact he.trans hd.symm

noncomputable instance (n : ℕ) : Fintype {p : NoncrossingFace n // IsPolygonFacet p} := by
  classical
  infer_instance

noncomputable def polygonDiagonal_facet_equiv (n : ℕ) :
    PolygonDiagonal n ≃ {p : NoncrossingFace n // IsPolygonFacet p} := by
  let f : PolygonDiagonal n → {p : NoncrossingFace n // IsPolygonFacet p} := fun d =>
    ⟨singletonPolygonFace d, (polygonFacet_iff_card_one _).mpr (Finset.card_singleton d)⟩
  apply Equiv.ofBijective f
  constructor
  · intro d e h
    have h' := congrArg (fun p => p.val.val) h
    exact Finset.singleton_injective h'
  · intro p
    obtain ⟨d, hd⟩ := Finset.card_eq_one.mp ((polygonFacet_iff_card_one p.val).mp p.property)
    refine ⟨d, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hd.symm

/-- When one input is added, the polygon gains exactly `n + 2` diagonals. -/
def polygonDiagonal_succ_equiv (n : ℕ) :
    PolygonDiagonal (n + 3) ≃ PolygonDiagonal (n + 2) ⊕ Fin (n + 2) where
  toFun d :=
    if hlast : d.b.val = n + 3 then
      .inr ⟨d.a.val, by have hg := d.gap; omega⟩
    else if hbase : d.a.val = 0 ∧ d.b.val = n + 2 then .inr 0
    else .inl
      ⟨⟨d.a.val, by have hb := d.b.isLt; have hg := d.gap; omega⟩,
        ⟨d.b.val, by have hb := d.b.isLt; omega⟩, d.gap, hbase⟩
  invFun d := match d with
    | .inl e =>
      ⟨⟨e.a.val, by have h := e.a.isLt; omega⟩,
        ⟨e.b.val, by have h := e.b.isLt; omega⟩, e.gap,
        by have h := e.b.isLt; dsimp; omega⟩
    | .inr k =>
      if hk : k.val = 0 then
        ⟨0, ⟨n + 2, by omega⟩, by simp, by simp⟩
      else
        ⟨⟨k.val, by have h := k.isLt; omega⟩, ⟨n + 3, by omega⟩,
          by have h := k.isLt; dsimp; omega, by simpa using hk⟩
  left_inv d := by
    have hb := d.b.isLt
    have ha := d.a.isLt
    have hg := d.gap
    have hn := d.not_boundary
    dsimp
    split_ifs <;> apply PolygonDiagonal.ext <;> apply Fin.ext <;> simp_all
  right_inv d := by
    cases d with
    | inl e =>
      have hb := e.b.isLt
      have hn := e.not_boundary
      dsimp
      rw [dif_neg (by omega), dif_neg hn]
    | inr k =>
      have hk := k.isLt
      dsimp
      split_ifs <;> dsimp at *
      all_goals first | omega | (congr 1; apply Fin.ext; dsimp; omega)

theorem polygonDiagonal_count_twice (n : ℕ) :
    2 * Fintype.card (PolygonDiagonal (n + 2)) = n * (n + 3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hc := Fintype.card_congr (polygonDiagonal_succ_equiv n)
    rw [Fintype.card_sum, Fintype.card_fin] at hc
    have he : n + 1 + 2 = n + 3 := by omega
    rw [he]
    nlinarith

theorem polygonDiagonal_count (n : ℕ) :
    Fintype.card (PolygonDiagonal (n + 2)) = n * (n + 3) / 2 := by
  have h := polygonDiagonal_count_twice n
  omega

/-- The general facet formula, counting maximal proper faces rather than labels. -/
theorem Kn_facet_count (n : ℕ) :
    Fintype.card {p : NoncrossingFace (n + 2) // IsPolygonFacet p} = n * (n + 3) / 2 := by
  rw [← Fintype.card_congr (polygonDiagonal_facet_equiv (n + 2)), polygonDiagonal_count]

/-- Rotate a left-associated triple, preserving every internal interval except
the interval joining its first two children. -/
private theorem rotate_left_spans (a b c : BinaryTree Unit) (start : ℕ) :
    (treeSpans (.node () (.node () a b) c) start).erase
        (start, start + a.numLeaves + b.numLeaves) ⊆
      treeSpans (.node () a (.node () b c)) start := by
  intro p hp
  simp only [treeSpans, BinaryTree.numLeaves, Finset.mem_erase, Finset.mem_insert,
    Finset.mem_union, Nat.add_assoc] at hp ⊢
  aesop

private theorem rotate_left_avoids (a b c : BinaryTree Unit) (start : ℕ) :
    (start, start + a.numLeaves + b.numLeaves) ∉
      treeSpans (.node () a (.node () b c)) start := by
  intro hp
  have he : (start + a.numLeaves, start + a.numLeaves + b.numLeaves + c.numLeaves) ∈
      treeSpans (.node () a (.node () b c)) start := by
    simp only [treeSpans, BinaryTree.numLeaves, Finset.mem_insert, Finset.mem_union,
      Nat.add_assoc]
    exact Or.inr (Or.inr (Or.inl trivial))
  have h := treeSpans_compatible (.node () a (.node () b c)) start _ hp _ he
  have ha := a.numLeaves_pos; have hb := b.numLeaves_pos; have hc := c.numLeaves_pos
  dsimp [SpanCompatible] at h
  omega

private theorem rotate_right_spans (a b c : BinaryTree Unit) (start : ℕ) :
    (treeSpans (.node () a (.node () b c)) start).erase
        (start + a.numLeaves, start + a.numLeaves + b.numLeaves + c.numLeaves) ⊆
      treeSpans (.node () (.node () a b) c) start := by
  intro p hp
  simp only [treeSpans, BinaryTree.numLeaves, Finset.mem_erase, Finset.mem_insert,
    Finset.mem_union, Nat.add_assoc] at hp ⊢
  aesop

private theorem rotate_right_avoids (a b c : BinaryTree Unit) (start : ℕ) :
    (start + a.numLeaves, start + a.numLeaves + b.numLeaves + c.numLeaves) ∉
      treeSpans (.node () (.node () a b) c) start := by
  intro hp
  have he : (start, start + a.numLeaves + b.numLeaves) ∈
      treeSpans (.node () (.node () a b) c) start := by
    simp only [treeSpans, BinaryTree.numLeaves, Finset.mem_insert, Finset.mem_union,
      Nat.add_assoc]
    exact Or.inr (Or.inl (Or.inl trivial))
  have h := treeSpans_compatible (.node () (.node () a b) c) start _ hp _ he
  have ha := a.numLeaves_pos; have hb := b.numLeaves_pos; have hc := c.numLeaves_pos
  dsimp [SpanCompatible] at h
  omega

/-- Any proper internal group can be changed by one rotation, with all other
groups retained. This prevents extra groups from being forced on a partial face. -/
theorem treeSpans_rotate_away (t : BinaryTree Unit) (start : ℕ) (p : BracketSpan)
    (hp : p ∈ treeSpans t start) (hproper : p ≠ (start, start + t.numLeaves)) :
    ∃ u : BinaryTree Unit, u.numLeaves = t.numLeaves ∧
      (treeSpans t start).erase p ⊆ treeSpans u start ∧ p ∉ treeSpans u start := by
  induction t generalizing start with
  | nil => simp [treeSpans] at hp
  | node val l r il ir =>
    cases val
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with hroot | hp | hp
    · exact False.elim (hproper (by simpa only [BinaryTree.numLeaves, Nat.add_assoc] using hroot))
    · by_cases he : p = (start, start + l.numLeaves)
      · cases l with
        | nil => have hv := treeSpans_valid (.nil : BinaryTree Unit) start p hp
                 dsimp [SpanValid] at hv; omega
        | node val a b =>
          cases val
          refine ⟨.node () a (.node () b r), by simp only [BinaryTree.numLeaves]; omega, ?_, ?_⟩
          · simpa only [he, BinaryTree.numLeaves, Nat.add_assoc] using rotate_left_spans a b r start
          · simpa only [he, BinaryTree.numLeaves, Nat.add_assoc] using
              rotate_left_avoids a b r start
      · obtain ⟨l', hn, hsub, hnot⟩ := il start hp he
        refine ⟨.node () l' r, by simp only [BinaryTree.numLeaves, hn], ?_, ?_⟩
        · intro q hq
          have hq' := Finset.mem_erase.mp hq
          simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hq' ⊢
          rcases hq'.2 with hroot | hq | hq
          · left; simpa only [hn] using hroot
          · right; left; exact hsub (Finset.mem_erase.mpr ⟨hq'.1, hq⟩)
          · right; right; simpa only [hn] using hq
        · intro hmem
          simp only [treeSpans, Finset.mem_insert, Finset.mem_union, hn] at hmem
          rcases hmem with hroot | hmem | hmem
          · exact hproper (by simpa only [BinaryTree.numLeaves, Nat.add_assoc] using hroot)
          · exact hnot hmem
          · have hv := treeSpans_valid l start p hp
            have hw := treeSpans_valid r (start + l.numLeaves) p hmem
            dsimp [SpanValid] at *; omega
    · by_cases he : p = (start + l.numLeaves, start + l.numLeaves + r.numLeaves)
      · cases r with
        | nil => have hv := treeSpans_valid (.nil : BinaryTree Unit) (start + l.numLeaves) p hp
                 dsimp [SpanValid] at hv; omega
        | node val b c =>
          cases val
          refine ⟨.node () (.node () l b) c, by simp only [BinaryTree.numLeaves]; omega, ?_, ?_⟩
          · simpa only [he, BinaryTree.numLeaves, Nat.add_assoc] using
              rotate_right_spans l b c start
          · simpa only [he, BinaryTree.numLeaves, Nat.add_assoc] using
              rotate_right_avoids l b c start
      · have he' : p ≠ (start + l.numLeaves, (start + l.numLeaves) + r.numLeaves) := he
        obtain ⟨r', hn, hsub, hnot⟩ := ir (start + l.numLeaves) hp he'
        refine ⟨.node () l r', by simp only [BinaryTree.numLeaves, hn], ?_, ?_⟩
        · intro q hq
          have hq' := Finset.mem_erase.mp hq
          simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hq' ⊢
          rcases hq'.2 with hroot | hq | hq
          · left; simpa only [hn] using hroot
          · right; left; exact hq
          · right; right; exact hsub (Finset.mem_erase.mpr ⟨hq'.1, hq⟩)
        · intro hmem
          simp only [treeSpans, Finset.mem_insert, Finset.mem_union, hn] at hmem
          rcases hmem with hroot | hmem | hmem
          · exact hproper (by simpa only [BinaryTree.numLeaves, Nat.add_assoc] using hroot)
          · have hv := treeSpans_valid r (start + l.numLeaves) p hp
            have hw := treeSpans_valid l start p hmem
            dsimp [SpanValid] at *; omega
          · exact hnot hmem

/-- A group absent from a partial pattern is absent from at least one completion. -/
theorem partialBracketing_completion_avoiding {n : ℕ} (hn : 2 ≤ n)
    (p : PartialBracketing n) (d : ProperBracket n) (hd : d ∉ p.val) :
    ∃ t : FullBracketing n, properBracketSpans p.val ⊆ treeSpans t.val 0 ∧
      bracketSpan d ∉ treeSpans t.val 0 := by
  have hs := spanFamily_insert_root hn (properBracketSpans_family p)
  obtain ⟨t, ht, hsub⟩ := spanFamily_complete n (by omega) 0 _ hs
  have hsub' : properBracketSpans p.val ⊆ treeSpans t 0 := by
    intro q hq; exact hsub (Finset.mem_insert_of_mem hq)
  by_cases hmem : bracketSpan d ∈ treeSpans t 0
  · have hproper : bracketSpan d ≠ (0, 0 + t.numLeaves) := by
      intro he
      apply d.proper
      have h := congrArg Prod.fst he
      have h' := congrArg Prod.snd he
      simpa only [bracketSpan, Nat.zero_add, ht] using And.intro h h'
    obtain ⟨u, hu, hus, hnot⟩ := treeSpans_rotate_away t 0 (bracketSpan d) hmem hproper
    refine ⟨⟨u, hu.trans ht⟩, ?_, hnot⟩
    intro q hq
    apply hus
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hq
      have hbd : b = d := bracketSpan_injective n (hbe.trans he)
      exact hd (hbd ▸ hb)
    · exact hsub' hq
  · exact ⟨⟨t, ht⟩, hsub', hmem⟩

end FunctorialGeometry
