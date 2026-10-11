/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralComposition
import Mathlib.Tactic

/-! # Directed tree rotations and their signed, path-dependent valuation -/

namespace FunctorialGeometry

abbrev BracketTree := BinaryTree Unit

inductive RightRotation : BracketTree → BracketTree → Prop
  | root (s t u : BracketTree) :
      RightRotation (.node () (.node () s t) u) (.node () s (.node () t u))
  | left {s t : BracketTree} (h : RightRotation s t) (u : BracketTree) :
      RightRotation (.node () s u) (.node () t u)
  | right {s t : BracketTree} (u : BracketTree) (h : RightRotation s t) :
      RightRotation (.node () u s) (.node () u t)

theorem RightRotation.numLeaves_eq {s t : BracketTree} (h : RightRotation s t) :
    s.numLeaves = t.numLeaves := by
  induction h with
  | root => simp [BinaryTree.numLeaves, Nat.add_assoc]
  | left h u ih => simp [BinaryTree.numLeaves, ih]
  | right u h ih => simp [BinaryTree.numLeaves, ih]

theorem RightRotation.numLeaves_ge_three {s t : BracketTree} (h : RightRotation s t) :
    3 ≤ s.numLeaves := by
  induction h with
  | root a b c =>
    have ha := a.numLeaves_pos
    have hb := b.numLeaves_pos
    have hc := c.numLeaves_pos
    simp only [BinaryTree.numLeaves]
    omega
  | left h u ih =>
    simp only [BinaryTree.numLeaves]
    omega
  | right u h ih =>
    simp only [BinaryTree.numLeaves]
    omega

inductive RotationStep : BracketTree → BracketTree → Type
  | right {s t : BracketTree} : RightRotation s t → RotationStep s t
  | left {s t : BracketTree} : RightRotation t s → RotationStep s t

def RotationStep.sign {s t : BracketTree} : RotationStep s t → ℤ
  | .right _ => 1
  | .left _ => -1

def RotationStep.reverse {s t : BracketTree} : RotationStep s t → RotationStep t s
  | .right h => .left h
  | .left h => .right h

@[simp] theorem RotationStep.sign_reverse {s t : BracketTree} (e : RotationStep s t) :
    e.reverse.sign = -e.sign := by cases e <;> rfl

inductive RotationPath : BracketTree → BracketTree → Type
  | nil (s : BracketTree) : RotationPath s s
  | cons {s t u : BracketTree} : RotationStep s t → RotationPath t u → RotationPath s u

def RotationPath.append {s t u : BracketTree} : RotationPath s t → RotationPath t u →
    RotationPath s u
  | .nil _, q => q
  | .cons e p, q => .cons e (p.append q)

@[simp] theorem RotationPath.append_nil {s t : BracketTree} (p : RotationPath s t) :
    p.append (.nil t) = p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [append, ih]

theorem RotationPath.append_assoc {s t u v : BracketTree}
    (p : RotationPath s t) (q : RotationPath t u) (r : RotationPath u v) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [append, ih]

def RotationPath.sign {s t : BracketTree} : RotationPath s t → ℤ
  | .nil _ => 0
  | .cons e p => e.sign + p.sign

def RotationPath.length {s t : BracketTree} : RotationPath s t → ℕ
  | .nil _ => 0
  | .cons _ p => 1 + p.length

@[simp] theorem RotationPath.sign_append {s t u : BracketTree}
    (p : RotationPath s t) (q : RotationPath t u) :
    (p.append q).sign = p.sign + q.sign := by
  induction p with
  | nil => simp [append, sign]
  | cons e p ih => simp [append, sign, ih, add_assoc]

@[simp] theorem RotationPath.length_append {s t u : BracketTree}
    (p : RotationPath s t) (q : RotationPath t u) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp [append, length]
  | cons e p ih => simp [append, length, ih, Nat.add_assoc]

def RotationPath.reverse {s t : BracketTree} : RotationPath s t → RotationPath t s
  | .nil s => .nil s
  | .cons e p => p.reverse.append (.cons e.reverse (.nil _))

@[simp] theorem RotationPath.sign_reverse {s t : BracketTree} (p : RotationPath s t) :
    p.reverse.sign = -p.sign := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [reverse, sign, ih]

@[simp] theorem RotationPath.length_reverse {s t : BracketTree} (p : RotationPath s t) :
    p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons e p ih => simp [reverse, length, ih, Nat.add_comm]

theorem RotationPath.numLeaves_eq {s t : BracketTree} (p : RotationPath s t) :
    s.numLeaves = t.numLeaves := by
  induction p with
  | nil => rfl
  | cons e p ih =>
      cases e with
      | right h => exact h.numLeaves_eq.trans ih
      | left h => exact h.numLeaves_eq.symm.trans ih

def RotationPath.valuation {s t : BracketTree} (p : RotationPath s t) : ℕ × ℤ :=
  (p.length, p.sign)

theorem RotationPath.valuation_append {s t u : BracketTree}
    (p : RotationPath s t) (q : RotationPath t u) :
    (p.append q).valuation = (p.length + q.length, p.sign + q.sign) := by
  simp [valuation]

def pentagonStart : BracketTree := .node () (.node () (.node () .nil .nil) .nil) .nil
def pentagonEnd : BracketTree := .node () .nil (.node () .nil (.node () .nil .nil))

def pentagonShortPath : RotationPath pentagonStart pentagonEnd :=
  .cons (.right (.root (.node () .nil .nil) .nil .nil))
    (.cons (.right (.root .nil .nil (.node () .nil .nil))) (.nil _))

def pentagonLongPath : RotationPath pentagonStart pentagonEnd :=
  .cons (.right (.left (.root .nil .nil .nil) .nil))
    (.cons (.right (.root .nil (.node () .nil .nil) .nil))
      (.cons (.right (.right .nil (.root .nil .nil .nil))) (.nil _)))

@[simp] theorem pentagonShortPath_sign : pentagonShortPath.sign = 2 := rfl
@[simp] theorem pentagonLongPath_sign : pentagonLongPath.sign = 3 := rfl

def pentagonClosedPath : RotationPath pentagonStart pentagonStart :=
  pentagonShortPath.append pentagonLongPath.reverse

theorem pentagonClosedPath_sign : pentagonClosedPath.sign = -1 := by
  simp [pentagonClosedPath]

theorem rotation_sign_path_dependent :
    ∃ (s t : BracketTree) (p q : RotationPath s t), p.sign ≠ q.sign := by
  exact ⟨pentagonStart, pentagonEnd, pentagonShortPath, pentagonLongPath, by decide⟩

theorem RotationPath.sign_eq_endpoint_difference (h : BracketTree → ℤ)
    (he : ∀ {s t : BracketTree} (e : RotationStep s t), e.sign = h t - h s)
    {s t : BracketTree} (p : RotationPath s t) : p.sign = h t - h s := by
  induction p with
  | nil => simp [sign]
  | cons e p ih => rw [sign, he e, ih]; ring

theorem rotation_sign_no_vertex_potential :
    ¬ ∃ h : BracketTree → ℤ,
      ∀ {s t : BracketTree} (e : RotationStep s t), e.sign = h t - h s := by
  rintro ⟨h, he⟩
  have hp := RotationPath.sign_eq_endpoint_difference h he pentagonClosedPath
  rw [pentagonClosedPath_sign] at hp
  omega

/-- Identifying the pentagon routes annihilates every additive image of the unit sign. -/
theorem pentagon_sign_additive_quotient_trivial {G : Type*} [AddCommGroup G]
    (f : ℤ →+ G) (he : f pentagonShortPath.sign = f pentagonLongPath.sign) : f = 0 := by
  have h23 : f 2 = f 3 := by simpa only [pentagonShortPath_sign, pentagonLongPath_sign] using he
  have hsum : f 3 = f 2 + f 1 := by simpa using f.map_add 2 1
  have hf1 : f 1 = 0 := by
    apply add_left_cancel (a := f 2)
    simpa only [add_zero, h23] using hsum.symm
  apply AddMonoidHom.ext
  intro z
  change f z = 0
  have hz := f.map_zsmul z (1 : ℤ)
  rw [hf1] at hz
  simpa only [zsmul_eq_mul, Int.cast_id, mul_one, smul_zero] using hz

end FunctorialGeometry
