/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralSignedDefects
import MathProject.DirectedReassociation
import MathProject.AssociahedralStructuralBridges

/-! # Axiom audit and cross-module checks for signed structural quantities -/

open FunctorialGeometry

#print axioms signedFaceDefect_formula
#print axioms completedFaceRank_pos
#print axioms signedFaceDefect_fullBracketings
#print axioms surroundingCompletedFace_sup
#print axioms surroundingCompletedFace_inf
#print axioms surroundingCompletedFace_rank
#print axioms surroundingCompletedFace_defect
#print axioms k4_signedDefect_positive
#print axioms k4_signedDefect_zero
#print axioms k4_signedDefect_negative
#print axioms completedFaceRank_K4_not_submodular
#print axioms completedFaceRank_K4_not_supermodular
#print axioms RightRotation.numLeaves_eq
#print axioms RotationPath.append_assoc
#print axioms RotationPath.sign_append
#print axioms RotationPath.sign_reverse
#print axioms RotationPath.valuation_append
#print axioms pentagonClosedPath_sign
#print axioms rotation_sign_path_dependent
#print axioms rotation_sign_no_vertex_potential
#print axioms Loday_bracketFace_dimension
#print axioms completedFaceRank_eq_geometric_dimension
#print axioms RightRotation.changed_span
#print axioms RightRotation.proper_bracket_intersection_card
#print axioms rightRotation_signedFaceDefect_zero
#print axioms rotationStep_signedFaceDefect_zero
#print axioms rightRotation_commonFace_dimension
#print axioms pentagon_sign_additive_quotient_trivial

-- A positive K4 defect survives embedding as a facet of K5.
example : signedFaceDefect
    (surroundingCompletedFace (by decide : 2 ≤ 4) (WithBot.some k4FaceAB))
    (surroundingCompletedFace (by decide : 2 ≤ 4) (WithBot.some k4FaceBC)) = 1 := by
  rw [surroundingCompletedFace_defect]
  exact k4_signedDefect_positive

-- Reversing the five-step closed walk reverses its nonzero sign.
example : pentagonClosedPath.reverse.sign = 1 := by
  rw [RotationPath.sign_reverse, pentagonClosedPath_sign]
  rfl

example : pentagonClosedPath.length = 5 := rfl

-- The combinatorial edge rank agrees with its actual geometric dimension.
example : LodayFaceDimension 2 (bracketExposedFace 2 k4FaceAB) = 1 := by
  have h := completedFaceRank_eq_geometric_dimension 2 k4FaceAB
  have hr : completedFaceRank (WithBot.some k4FaceAB) = 2 := by decide
  rw [hr] at h
  omega

-- The defect bridge also covers a rotation inside a proper subtree.
example : signedFaceDefect (WithBot.some k4VertexLeft)
    (WithBot.some (treePartialBracketing
      (⟨.node () (.node () .nil (.node () .nil .nil)) .nil, rfl⟩ : FullBracketing 4))) = 0 := by
  change signedFaceDefect
    (WithBot.some (treePartialBracketing (⟨pentagonStart, rfl⟩ : FullBracketing 4))) _ = 0
  exact rightRotation_signedFaceDefect_zero (by decide) _ _
    (.left (.root .nil .nil .nil) .nil)
