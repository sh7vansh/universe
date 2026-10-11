/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.FunctorialGeometry
import Mathlib.Order.WithBot

/-! # Signed modularity on the completed associahedral face lattice -/

namespace FunctorialGeometry

abbrev BracketFamily {n : ℕ} (s : Finset (ProperBracket n)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, BracketCompatible p q

theorem bracketFamily_subset {n : ℕ} {s t : Finset (ProperBracket n)}
    (ht : BracketFamily t) (h : s ⊆ t) : BracketFamily s :=
  fun p hp q hq => ht p (h hp) q (h hq)

instance {n : ℕ} : DecidableRel (@BracketCompatible n) := fun _ _ => by
  unfold BracketCompatible
  infer_instance

instance {n : ℕ} (s : Finset (ProperBracket n)) : Decidable (BracketFamily s) :=
  inferInstanceAs (Decidable (∀ p ∈ s, ∀ q ∈ s, BracketCompatible p q))

def bracketIntersection {n : ℕ} (s t : PartialBracketing n) : PartialBracketing n :=
  ⟨s.val ∩ t.val, bracketFamily_subset s.property Finset.inter_subset_left⟩

/-- Empty geometric face adjoined to the existing nonempty face order. -/
abbrev CompletedBracketing (n : ℕ) := WithBot (PartialBracketing n)

theorem completed_coe_le_iff {n : ℕ} (s t : PartialBracketing n) :
    (WithBot.some s : CompletedBracketing n) ≤ WithBot.some t ↔ t.val ⊆ s.val :=
  WithBot.coe_le_coe (α := PartialBracketing n)

def completedSup {n : ℕ} : CompletedBracketing n → CompletedBracketing n →
    CompletedBracketing n
  | ⊥, t => t
  | s, ⊥ => s
  | (s : PartialBracketing n), (t : PartialBracketing n) => WithBot.some (bracketIntersection s t)

noncomputable def completedInf {n : ℕ} : CompletedBracketing n → CompletedBracketing n →
    CompletedBracketing n
  | ⊥, _ => ⊥
  | _, ⊥ => ⊥
  | (s : PartialBracketing n), (t : PartialBracketing n) =>
      if h : BracketFamily (s.val ∪ t.val) then
        WithBot.some (⟨s.val ∪ t.val, h⟩ : PartialBracketing n)
      else ⊥

noncomputable instance (n : ℕ) : Lattice (CompletedBracketing n) where
  sup := completedSup
  inf := completedInf
  le_sup_left := by
    intro a b
    cases a with
    | none => exact bot_le
    | some s =>
      cases b with
      | none => exact le_rfl
      | some t =>
        exact (completed_coe_le_iff s (bracketIntersection s t)).mpr Finset.inter_subset_left
  le_sup_right := by
    intro a b
    cases a with
    | none => exact le_rfl
    | some s =>
      cases b with
      | none => exact bot_le
      | some t =>
        exact (completed_coe_le_iff t (bracketIntersection s t)).mpr Finset.inter_subset_right
  sup_le := by
    intro a b c ha hb
    cases a with
    | none => exact hb
    | some s =>
      cases b with
      | none => exact ha
      | some t =>
        cases c with
        | none => exact False.elim ((WithBot.not_coe_le_bot s) ha)
        | some u =>
          exact (completed_coe_le_iff (bracketIntersection s t) u).mpr
            (Finset.subset_inter ((completed_coe_le_iff s u).mp ha)
              ((completed_coe_le_iff t u).mp hb))
  inf_le_left := by
    intro a b
    cases a with
    | none => exact le_rfl
    | some s =>
      cases b with
      | none => exact bot_le
      | some t =>
        change completedInf (WithBot.some s) (WithBot.some t) ≤ WithBot.some s
        simp only [completedInf]
        split_ifs with h
        · apply (completed_coe_le_iff _ s).mpr
          exact Finset.subset_union_left
        · exact bot_le
  inf_le_right := by
    intro a b
    cases a with
    | none => exact bot_le
    | some s =>
      cases b with
      | none => exact le_rfl
      | some t =>
        change completedInf (WithBot.some s) (WithBot.some t) ≤ WithBot.some t
        simp only [completedInf]
        split_ifs with h
        · apply (completed_coe_le_iff _ t).mpr
          exact Finset.subset_union_right
        · exact bot_le
  le_inf := by
    intro a b c hb hc
    cases a with
    | none => exact bot_le
    | some s =>
      cases b with
      | none => exact False.elim ((WithBot.not_coe_le_bot s) hb)
      | some t =>
        cases c with
        | none => exact False.elim ((WithBot.not_coe_le_bot s) hc)
        | some u =>
          have hsub : t.val ∪ u.val ⊆ s.val := Finset.union_subset
            ((completed_coe_le_iff s t).mp hb) ((completed_coe_le_iff s u).mp hc)
          have hcompat := bracketFamily_subset s.property hsub
          change (WithBot.some s : CompletedBracketing n) ≤
            completedInf (WithBot.some t) (WithBot.some u)
          simp only [completedInf, dif_pos hcompat]
          exact (completed_coe_le_iff s _).mpr hsub

def completedFaceRank {n : ℕ} : CompletedBracketing n → ℤ
  | ⊥ => 0
  | (s : PartialBracketing n) => (n : ℤ) - 1 - s.val.card

noncomputable def signedFaceDefect {n : ℕ} (s t : CompletedBracketing n) : ℤ :=
  modularityDefect completedFaceRank s t

@[simp] theorem signedFaceDefect_bot_left {n : ℕ} (t : CompletedBracketing n) :
    signedFaceDefect ⊥ t = 0 := by
  simp [signedFaceDefect, modularityDefect, completedFaceRank]

@[simp] theorem signedFaceDefect_bot_right {n : ℕ} (s : CompletedBracketing n) :
    signedFaceDefect s ⊥ = 0 := by
  rw [signedFaceDefect, modularityDefect_comm]
  exact signedFaceDefect_bot_left s

theorem signedFaceDefect_formula {n : ℕ} (s t : PartialBracketing n) :
    signedFaceDefect (WithBot.some s) (WithBot.some t) =
      if BracketFamily (s.val ∪ t.val) then 0 else (n : ℤ) - 1 - (s.val ∪ t.val).card := by
  classical
  have hc := Finset.card_union_add_card_inter s.val t.val
  have hci : ((s.val ∪ t.val).card : ℤ) + (s.val ∩ t.val).card =
      s.val.card + t.val.card := by exact_mod_cast hc
  unfold signedFaceDefect modularityDefect
  change completedFaceRank (WithBot.some s) + completedFaceRank (WithBot.some t) -
    (completedFaceRank (completedSup (WithBot.some s) (WithBot.some t)) +
      completedFaceRank (completedInf (WithBot.some s) (WithBot.some t))) = _
  by_cases h : BracketFamily (s.val ∪ t.val)
  · simp only [completedSup, completedInf, dif_pos h, completedFaceRank,
      bracketIntersection, if_pos h]
    omega
  · simp only [completedSup, completedInf, dif_neg h, completedFaceRank,
      bracketIntersection, if_neg h]
    omega

theorem completedFaceRank_pos {n : ℕ} (hn : 2 ≤ n) (s : PartialBracketing n) :
    1 ≤ completedFaceRank (WithBot.some s) := by
  have h := partialBracketing_card_le hn s
  change 1 ≤ (n : ℤ) - 1 - s.val.card
  omega

def surroundingBracket {n : ℕ} (p : ProperBracket n) : ProperBracket (n + 1) where
  left := ⟨p.left.val, by have := p.left.isLt; omega⟩
  right := ⟨p.right.val, by have := p.right.isLt; omega⟩
  length_two := p.length_two
  proper := by
    change ¬ (p.left.val = 0 ∧ p.right.val = n + 1)
    have := p.right.isLt
    omega

def surroundingBracketEmbedding (n : ℕ) : ProperBracket n ↪ ProperBracket (n + 1) where
  toFun := surroundingBracket
  inj' := by
    intro p q h
    apply ProperBracket.ext <;> apply Fin.ext
    · exact congrArg (fun b => b.left.val) h
    · exact congrArg (fun b => b.right.val) h

def surroundingRoot (n : ℕ) (hn : 2 ≤ n) : ProperBracket (n + 1) where
  left := ⟨0, by omega⟩
  right := ⟨n, by omega⟩
  length_two := hn
  proper := by
    change ¬ (0 = 0 ∧ n = n + 1)
    omega

@[simp] theorem surroundingBracket_compatible {n : ℕ} (p q : ProperBracket n) :
    BracketCompatible (surroundingBracket p) (surroundingBracket q) ↔
      BracketCompatible p q := Iff.rfl

theorem surroundingRoot_compatible {n : ℕ} (hn : 2 ≤ n) (p : ProperBracket n) :
    BracketCompatible (surroundingRoot n hn) (surroundingBracket p) ∧
      BracketCompatible (surroundingBracket p) (surroundingRoot n hn) := by
  have := p.right.isLt
  simp only [BracketCompatible, surroundingRoot, surroundingBracket]
  omega

def surroundingBrackets {n : ℕ} (hn : 2 ≤ n) (s : Finset (ProperBracket n)) :
    Finset (ProperBracket (n + 1)) :=
  insert (surroundingRoot n hn) (s.map (surroundingBracketEmbedding n))

theorem surroundingRoot_not_mem {n : ℕ} (hn : 2 ≤ n) (s : Finset (ProperBracket n)) :
    surroundingRoot n hn ∉ s.map (surroundingBracketEmbedding n) := by
  intro h
  obtain ⟨p, _, hp⟩ := Finset.mem_map.mp h
  have hl : p.left.val = 0 := congrArg (fun b => b.left.val) hp
  have hr : p.right.val = n := congrArg (fun b => b.right.val) hp
  exact p.proper ⟨hl, hr⟩

theorem surroundingBrackets_card {n : ℕ} (hn : 2 ≤ n) (s : Finset (ProperBracket n)) :
    (surroundingBrackets hn s).card = s.card + 1 := by
  unfold surroundingBrackets
  rw [Finset.card_insert_of_notMem (surroundingRoot_not_mem hn s), Finset.card_map]

theorem surroundingBrackets_compatible_iff {n : ℕ} (hn : 2 ≤ n)
    (s : Finset (ProperBracket n)) : BracketFamily (surroundingBrackets hn s) ↔
      BracketFamily s := by
  constructor
  · intro h p hp q hq
    apply (surroundingBracket_compatible p q).mp
    exact h _ (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨p, hp, rfl⟩))
      _ (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨q, hq, rfl⟩))
  · intro h p hp q hq
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · unfold BracketCompatible; omega
      · obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hq
        exact (surroundingRoot_compatible hn q).1
    · obtain ⟨p, hps, rfl⟩ := Finset.mem_map.mp hp
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact (surroundingRoot_compatible hn p).2
      · obtain ⟨q, hqs, rfl⟩ := Finset.mem_map.mp hq
        exact (surroundingBracket_compatible p q).mpr (h p hps q hqs)

@[simp] theorem surroundingBrackets_union {n : ℕ} (hn : 2 ≤ n)
    (s t : Finset (ProperBracket n)) :
    surroundingBrackets hn (s ∪ t) = surroundingBrackets hn s ∪ surroundingBrackets hn t := by
  simp [surroundingBrackets, Finset.map_union]

@[simp] theorem surroundingBrackets_inter {n : ℕ} (hn : 2 ≤ n)
    (s t : Finset (ProperBracket n)) :
    surroundingBrackets hn (s ∩ t) = surroundingBrackets hn s ∩ surroundingBrackets hn t := by
  unfold surroundingBrackets
  rw [Finset.map_inter]
  ext p
  simp only [Finset.mem_insert, Finset.mem_inter]
  tauto

def surroundingFace {n : ℕ} (hn : 2 ≤ n) (s : PartialBracketing n) :
    PartialBracketing (n + 1) :=
  ⟨surroundingBrackets hn s.val, (surroundingBrackets_compatible_iff hn s.val).mpr s.property⟩

def surroundingCompletedFace {n : ℕ} (hn : 2 ≤ n) : CompletedBracketing n →
    CompletedBracketing (n + 1)
  | ⊥ => ⊥
  | (s : PartialBracketing n) => WithBot.some (surroundingFace hn s)

@[simp] theorem surroundingCompletedFace_rank {n : ℕ} (hn : 2 ≤ n)
    (s : CompletedBracketing n) :
    completedFaceRank (surroundingCompletedFace hn s) = completedFaceRank s := by
  cases s with
  | none => rfl
  | some s =>
    simp only [surroundingCompletedFace, completedFaceRank, surroundingFace,
      surroundingBrackets_card]
    push_cast
    ring

theorem surroundingCompletedFace_sup {n : ℕ} (hn : 2 ≤ n)
    (s t : CompletedBracketing n) :
    surroundingCompletedFace hn (s ⊔ t) =
      surroundingCompletedFace hn s ⊔ surroundingCompletedFace hn t := by
  cases s with
  | none => rfl
  | some s =>
    cases t with
    | none => rfl
    | some t =>
      change WithBot.some (surroundingFace hn (bracketIntersection s t)) =
        WithBot.some (bracketIntersection (surroundingFace hn s) (surroundingFace hn t))
      congr 1
      apply Subtype.ext
      exact surroundingBrackets_inter hn s.val t.val

theorem surroundingCompletedFace_inf {n : ℕ} (hn : 2 ≤ n)
    (s t : CompletedBracketing n) :
    surroundingCompletedFace hn (s ⊓ t) =
      surroundingCompletedFace hn s ⊓ surroundingCompletedFace hn t := by
  cases s with
  | none => rfl
  | some s =>
    cases t with
    | none => rfl
    | some t =>
      have hc : BracketFamily ((surroundingFace hn s).val ∪ (surroundingFace hn t).val) ↔
          BracketFamily (s.val ∪ t.val) := by
        change BracketFamily (surroundingBrackets hn s.val ∪ surroundingBrackets hn t.val) ↔ _
        rw [← surroundingBrackets_union]
        exact surroundingBrackets_compatible_iff hn _
      change surroundingCompletedFace hn (completedInf (WithBot.some s) (WithBot.some t)) =
        completedInf (WithBot.some (surroundingFace hn s)) (WithBot.some (surroundingFace hn t))
      by_cases h : BracketFamily (s.val ∪ t.val)
      · simp only [completedInf, dif_pos h, dif_pos (hc.mpr h), surroundingCompletedFace]
        congr 1
        apply Subtype.ext
        exact surroundingBrackets_union hn s.val t.val
      · simp only [completedInf, dif_neg h, dif_neg (fun h' => h (hc.mp h')),
          surroundingCompletedFace]

theorem surroundingCompletedFace_defect {n : ℕ} (hn : 2 ≤ n)
    (s t : CompletedBracketing n) :
    signedFaceDefect (surroundingCompletedFace hn s) (surroundingCompletedFace hn t) =
      signedFaceDefect s t := by
  unfold signedFaceDefect modularityDefect
  rw [← surroundingCompletedFace_sup, ← surroundingCompletedFace_inf]
  simp only [surroundingCompletedFace_rank]

theorem fullBracketing_union_incompatible {n : ℕ} (hn : 2 ≤ n)
    (s t : FullBracketing n) (hne : s ≠ t) :
    ¬ BracketFamily ((treePartialBracketing s).val ∪ (treePartialBracketing t).val) := by
  intro h
  let u : PartialBracketing n :=
    ⟨(treePartialBracketing s).val ∪ (treePartialBracketing t).val, h⟩
  have hs : u = treePartialBracketing s :=
    treePartialBracketing_vertex hn s u Finset.subset_union_left
  have ht : u = treePartialBracketing t :=
    treePartialBracketing_vertex hn t u Finset.subset_union_right
  exact hne ((treePartialBracketing_injective hn) (hs.symm.trans ht))

theorem signedFaceDefect_fullBracketings {n : ℕ} (hn : 2 ≤ n)
    (s t : FullBracketing n) (hne : s ≠ t) :
    signedFaceDefect (WithBot.some (treePartialBracketing s))
        (WithBot.some (treePartialBracketing t)) =
      3 - (n : ℤ) + ((treePartialBracketing s).val ∩ (treePartialBracketing t).val).card := by
  rw [signedFaceDefect_formula, if_neg (fullBracketing_union_incompatible hn s t hne)]
  have hs := treeProperSpans_card hn s
  have ht := treeProperSpans_card hn t
  have hc := Finset.card_union_add_card_inter (treePartialBracketing s).val
    (treePartialBracketing t).val
  omega

def k4BracketAB : ProperBracket 4 := ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide, by decide⟩
def k4BracketBC : ProperBracket 4 := ⟨⟨1, by decide⟩, ⟨3, by decide⟩, by decide, by decide⟩
def k4BracketCD : ProperBracket 4 := ⟨⟨2, by decide⟩, ⟨4, by decide⟩, by decide, by decide⟩
def k4BracketABC : ProperBracket 4 := ⟨⟨0, by decide⟩, ⟨3, by decide⟩, by decide, by decide⟩
def k4BracketBCD : ProperBracket 4 := ⟨⟨1, by decide⟩, ⟨4, by decide⟩, by decide, by decide⟩

def k4FaceAB : PartialBracketing 4 := ⟨{k4BracketAB}, by decide⟩
def k4FaceBC : PartialBracketing 4 := ⟨{k4BracketBC}, by decide⟩
def k4FaceCD : PartialBracketing 4 := ⟨{k4BracketCD}, by decide⟩
def k4VertexLeft : PartialBracketing 4 := ⟨{k4BracketAB, k4BracketABC}, by decide⟩
def k4VertexRight : PartialBracketing 4 := ⟨{k4BracketCD, k4BracketBCD}, by decide⟩

theorem k4_signedDefect_positive :
    signedFaceDefect (WithBot.some k4FaceAB) (WithBot.some k4FaceBC) = 1 := by decide

theorem k4_signedDefect_zero :
    signedFaceDefect (WithBot.some k4FaceAB) (WithBot.some k4FaceCD) = 0 := by decide

theorem k4_signedDefect_negative :
    signedFaceDefect (WithBot.some k4VertexLeft) (WithBot.some k4VertexRight) = -1 := by decide

theorem completedFaceRank_K4_not_submodular :
    ¬ ∀ s t : CompletedBracketing 4, 0 ≤ signedFaceDefect s t := by
  intro h
  have hh := h (WithBot.some k4VertexLeft) (WithBot.some k4VertexRight)
  rw [k4_signedDefect_negative] at hh
  omega

theorem completedFaceRank_K4_not_supermodular :
    ¬ ∀ s t : CompletedBracketing 4, signedFaceDefect s t ≤ 0 := by
  intro h
  have hh := h (WithBot.some k4FaceAB) (WithBot.some k4FaceBC)
  rw [k4_signedDefect_positive] at hh
  omega

end FunctorialGeometry
