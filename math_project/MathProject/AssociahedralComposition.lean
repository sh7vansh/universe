/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Mathlib.Data.Finset.Image

/-!
# Associahedral composition in every arity

A proper bracket groups the consecutive inputs in a half-open interval `[left, right)`.
Two brackets can occur together precisely when the intervals are disjoint or nested.
The map `[a, b) ↦ (a, b)` identifies these patterns with noncrossing diagonal sets
in a polygon with `n + 1` vertices. Reverse inclusion gives the nonempty face order
of the **combinatorial** associahedron `K_n`, for `n ≥ 2`.

`KnFace 0 = Empty` and `KnFace 1` has one element. These are explicit nullary and
unary conventions, not applications of the dimension formula `n - 2`.

This module proves the bracket-to-polygon order isomorphism and the binary-tree count.
`AssociahedralTrees` identifies binary trees with the minimal polygon faces.
`AssociahedralRealization` constructs Loday's convex hull and classifies its extreme points.
`AssociahedralFaces` proves its full nonempty supporting-face order isomorphism.
`AssociahedralDimension` proves the actual affine dimension and geometric facet count.
-/

namespace FunctorialGeometry

open CategoryTheory

/-- A proper group of at least two consecutive inputs, excluding the whole word. -/
@[ext]
structure ProperBracket (n : ℕ) where
  left : Fin (n + 1)
  right : Fin (n + 1)
  length_two : left.val + 2 ≤ right.val
  proper : ¬ (left.val = 0 ∧ right.val = n)
  deriving DecidableEq

/-- Two bracket groups can occur together if they are disjoint or nested. -/
def BracketCompatible {n : ℕ} (p q : ProperBracket n) : Prop :=
  p.right.val ≤ q.left.val ∨ q.right.val ≤ p.left.val ∨
  (p.left.val ≤ q.left.val ∧ q.right.val ≤ p.right.val) ∨
  (q.left.val ≤ p.left.val ∧ p.right.val ≤ q.right.val)

/-- A diagonal in a polygon with `n + 1` cyclically ordered vertices. -/
@[ext]
structure PolygonDiagonal (n : ℕ) where
  a : Fin (n + 1)
  b : Fin (n + 1)
  gap : a.val + 2 ≤ b.val
  not_boundary : ¬ (a.val = 0 ∧ b.val = n)
  deriving DecidableEq

/-- Strict interleaving of endpoints means that the interiors cross. -/
def DiagonalsCross {n : ℕ} (d e : PolygonDiagonal n) : Prop :=
  (d.a.val < e.a.val ∧ e.a.val < d.b.val ∧ d.b.val < e.b.val) ∨
  (e.a.val < d.a.val ∧ d.a.val < e.b.val ∧ e.b.val < d.b.val)

instance (n : ℕ) : DecidableRel (@DiagonalsCross n) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

instance (n : ℕ) : Fintype (PolygonDiagonal n) :=
  Fintype.ofEquiv
    {p : Fin (n + 1) × Fin (n + 1) //
      p.1.val + 2 ≤ p.2.val ∧ ¬ (p.1.val = 0 ∧ p.2.val = n)}
    { toFun p := ⟨p.val.1, p.val.2, p.property.1, p.property.2⟩
      invFun d := ⟨(d.a, d.b), d.gap, d.not_boundary⟩
      left_inv p := by cases p; rfl
      right_inv d := by cases d; rfl }

/-- A bracket interval determines the chord with the same endpoints. -/
def bracketDiagonalEquiv (n : ℕ) : ProperBracket n ≃ PolygonDiagonal n where
  toFun p := ⟨p.left, p.right, p.length_two, p.proper⟩
  invFun d := ⟨d.a, d.b, d.gap, d.not_boundary⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The substantive compatibility bridge: laminar intervals are noncrossing chords. -/
theorem bracketCompatible_iff_noncrossing {n : ℕ} (p q : ProperBracket n) :
    BracketCompatible p q ↔
      ¬ DiagonalsCross (bracketDiagonalEquiv n p) (bracketDiagonalEquiv n q) := by
  have hp := p.length_two
  have hq := q.length_two
  dsimp [BracketCompatible, DiagonalsCross, bracketDiagonalEquiv]
  omega

/-- Compatible partial bracket patterns, ordered by adding brackets. -/
abbrev PartialBracketing (n : ℕ) :=
  OrderDual {s : Finset (ProperBracket n) //
    ∀ p ∈ s, ∀ q ∈ s, BracketCompatible p q}

/-- Nonempty combinatorial faces, ordered by reverse inclusion of diagonal sets.
The empty set of diagonals denotes the whole associahedron, not the empty face. -/
abbrev NoncrossingFace (n : ℕ) :=
  OrderDual {s : Finset (PolygonDiagonal n) //
    ∀ d ∈ s, ∀ e ∈ s, ¬ DiagonalsCross d e}

private theorem bracketPatterns_map_iff (n : ℕ) (s : Finset (ProperBracket n)) :
    (∀ p ∈ s, ∀ q ∈ s, BracketCompatible p q) ↔
      (∀ d ∈ s.map (bracketDiagonalEquiv n).toEmbedding,
        ∀ e ∈ s.map (bracketDiagonalEquiv n).toEmbedding, ¬ DiagonalsCross d e) := by
  constructor
  · intro h d hd e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hd
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp he
    exact (bracketCompatible_iff_noncrossing p q).mp (h p hp q hq)
  · intro h p hp q hq
    apply (bracketCompatible_iff_noncrossing p q).mpr
    exact h _ (Finset.mem_map.mpr ⟨p, hp, rfl⟩)
      _ (Finset.mem_map.mpr ⟨q, hq, rfl⟩)

/-- For every arity, partial bracket patterns and polygon faces have the same order. -/
def partialBracketing_face_orderIso (n : ℕ) :
    PartialBracketing n ≃o NoncrossingFace n where
  toEquiv := (bracketDiagonalEquiv n).finsetCongr.subtypeEquiv
    (bracketPatterns_map_iff n)
  map_rel_iff' := by
    intro s t
    change t.val.map (bracketDiagonalEquiv n).toEmbedding ⊆
      s.val.map (bracketDiagonalEquiv n).toEmbedding ↔ t.val ⊆ s.val
    exact Finset.map_subset_map

/-- The full family, with an empty nullary member and a unary unit member. -/
def KnFace : ℕ → Type
  | 0 => Empty
  | n + 1 => NoncrossingFace (n + 1)

/-- The same nullary convention on the bracket side. -/
def KnBracketing : ℕ → Type
  | 0 => Empty
  | n + 1 => PartialBracketing (n + 1)

instance (n : ℕ) : PartialOrder (KnFace n) := by
  cases n <;> unfold KnFace <;> infer_instance

instance (n : ℕ) : PartialOrder (KnBracketing n) := by
  cases n <;> unfold KnBracketing <;> infer_instance

instance (n : ℕ) : Fintype (KnFace n) := by
  cases n <;> unfold KnFace <;> infer_instance

/-- The bracket-to-face theorem for every `K_n`, including the stated conventions. -/
def all_Kn_orderIso : (n : ℕ) → KnBracketing n ≃o KnFace n
  | 0 => OrderIso.refl Empty
  | n + 1 => partialBracketing_face_orderIso (n + 1)

/-- The order isomorphism also identifies the associated thin categories. -/
def all_Kn_categoryEquivalence (n : ℕ) : KnBracketing n ≌ KnFace n :=
  (all_Kn_orderIso n).equivalence

/-- There is no proper bracket on a word of one input. -/
theorem no_unary_bracket (p : ProperBracket 1) : False := by
  have h := p.length_two
  have hr := p.right.isLt
  have hl := p.left.isLt
  have hp := p.proper
  omega

/-- The unary member is exactly one element under our unit convention. -/
def K1_equiv_unit : KnFace 1 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨∅, by simp⟩
  left_inv s := by
    apply Subtype.ext
    symm
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d _
    exact no_unary_bracket ((bracketDiagonalEquiv 1).symm d)
  right_inv _ := rfl

/-- These counts include the whole polytope and exclude its empty face. -/
theorem K0_face_count : Fintype.card (KnFace 0) = 0 := by decide

theorem K1_face_count : Fintype.card (KnFace 1) = 1 := by decide

theorem K2_face_count : Fintype.card (KnFace 2) = 1 := by decide

theorem K3_face_count : Fintype.card (KnFace 3) = 3 := by decide

set_option maxRecDepth 4096 in
theorem K4_face_count : Fintype.card (KnFace 4) = 11 := by decide

/-- A full binary bracketing of `n` inputs. Zero inputs have no binary tree. -/
def FullBracketing (n : ℕ) := {t : BinaryTree Unit // t.numLeaves = n}

private def fullBracketingEquiv (n : ℕ) :
    FullBracketing (n + 1) ≃ ↥(BinaryTree.treesOfNumNodesEq n) :=
  (Equiv.refl (BinaryTree Unit)).subtypeEquiv (fun t => by
    simp only [Equiv.refl_apply, BinaryTree.mem_treesOfNumNodesEq,
      BinaryTree.numLeaves_eq_numNodes_succ, Nat.add_right_cancel_iff])

instance (n : ℕ) : Fintype (FullBracketing (n + 1)) :=
  Fintype.ofEquiv _ (fullBracketingEquiv n).symm

/-- The Catalan count of full bracketings in every positive arity. -/
theorem fullBracketing_card (n : ℕ) :
    Fintype.card (FullBracketing (n + 1)) = catalan n := by
  rw [Fintype.card_congr (fullBracketingEquiv n), Fintype.card_coe,
    BinaryTree.treesOfNumNodesEq_card_eq_catalan]

/-- Closed formula: `C_n = choose (2*n) n / (n+1)`. Division is exact here. -/
theorem fullBracketing_card_formula (n : ℕ) :
    Fintype.card (FullBracketing (n + 1)) = Nat.choose (2 * n) n / (n + 1) := by
  rw [fullBracketing_card, catalan_eq_centralBinom_div]
  rfl

/-- There is no full binary bracketing of zero inputs. -/
theorem no_nullary_fullBracketing (t : FullBracketing 0) : False := by
  have h := t.val.numLeaves_pos
  rw [t.property] at h
  omega

section Evaluation

variable {L : Type*} [PartialOrder L]

/-- Evaluate a tree by actual categorical composition, using consecutive chain arrows. -/
def evalBracketTree (x : ℕ → L) (hx : Monotone x) :
    (t : BinaryTree Unit) → (start : ℕ) → (x start ⟶ x (start + t.numLeaves))
  | .nil, start => homOfLE (hx (by simp))
  | .node _ a b, start => by
    have f := evalBracketTree x hx a start
    have g := evalBracketTree x hx b (start + a.numLeaves)
    simpa only [BinaryTree.numLeaves, Nat.add_assoc] using f ≫ g

/-- Every tree evaluates to the unique chain arrow. -/
theorem evalBracketTree_eq (x : ℕ → L) (hx : Monotone x)
    (t : BinaryTree Unit) (start : ℕ) :
    evalBracketTree x hx t start = homOfLE (hx (Nat.le_add_right _ _)) :=
  Subsingleton.elim _ _

/-- Evaluate a full bracketing to a morphism with the common endpoints. -/
def evalFullBracketing (x : ℕ → L) (hx : Monotone x) {n : ℕ}
    (t : FullBracketing n) (start : ℕ) : x start ⟶ x (start + n) := by
  have f := evalBracketTree x hx t.val start
  simpa only [t.property] using f

/-- In every arity, any two full bracketings have the same composite. -/
theorem all_bracketings_same_composite (x : ℕ → L) (hx : Monotone x)
    {n : ℕ} (s t : FullBracketing n) (start : ℕ) :
    evalFullBracketing x hx s start = evalFullBracketing x hx t start :=
  Subsingleton.elim _ _

/-- Extend a finite chain by repeating its last object. -/
def extendFiniteChain {n : ℕ} (x : Fin (n + 1) → L) (i : ℕ) : L :=
  x ⟨min i n, by omega⟩

theorem extendFiniteChain_monotone {n : ℕ} (x : Fin (n + 1) → L)
    (hx : Monotone x) : Monotone (extendFiniteChain x) := by
  intro i j hij
  apply hx
  exact min_le_min_right n hij

/-- Evaluate a bracketing of a finite chain of exactly `n` arrows. -/
def evalChainBracketing {n : ℕ} (x : Fin (n + 1) → L) (hx : Monotone x)
    (t : FullBracketing n) : x 0 ⟶ x (Fin.last n) := by
  simpa [extendFiniteChain, Fin.last] using
    evalFullBracketing (extendFiniteChain x) (extendFiniteChain_monotone x hx) t 0

/-- The thin-category conclusion for every finite chain and every positive arity. -/
theorem all_Kn_chain_composites {n : ℕ} (x : Fin (n + 1) → L)
    (hx : Monotone x) (s t : FullBracketing n) :
    evalChainBracketing x hx s = evalChainBracketing x hx t :=
  Subsingleton.elim _ _

/-- The general theorem: bracket and face orders agree, while evaluation identifies
all full bracketings of the given chain. The face construction retains the syntax. -/
theorem all_Kn_thin_composition (n : ℕ) (x : Fin (n + 1) → L) (hx : Monotone x) :
    Nonempty (KnBracketing n ≃o KnFace n) ∧
      ∀ s t : FullBracketing n, evalChainBracketing x hx s = evalChainBracketing x hx t :=
  ⟨⟨all_Kn_orderIso n⟩, fun s t => all_Kn_chain_composites x hx s t⟩

/-- Nullary composition is the identity arrow. -/
def evalNullary (x : L) : x ⟶ x := 𝟙 x

end Evaluation

end FunctorialGeometry
