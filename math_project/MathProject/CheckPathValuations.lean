/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.FunctorialGeometry

/-! # Axiom audit and labelled path checks -/

open FunctorialGeometry

#print axioms pathExperience_action
#print axioms pathExperience_label
#print axioms evalBracketPath_eq
#print axioms chainSteps_valuation
#print axioms evalChainPathBracketing_unit_cost
#print axioms all_Kn_chain_path_valuations

private def labelledSteps : List (LatticeStep ℕ) :=
  [⟨0, 1, by decide, 2, 4⟩,
   ⟨1, 2, by decide, 3, -7⟩,
   ⟨2, 3, by decide, 5, 1⟩]

-- Negative labels can cancel. Both ternary patterns still give the same total.
example :
    evalBracketPath labelledSteps (.node () (.node () .nil .nil) .nil) = ⟨10, ⟨-2⟩⟩ ∧
    evalBracketPath labelledSteps (.node () .nil (.node () .nil .nil)) = ⟨10, ⟨-2⟩⟩ := by
  decide

-- The empty path has the identity valuation.
example : pathExperience ([] : List (LatticeStep ℕ)) = ⟨0, ⟨0⟩⟩ := rfl

-- Equal endpoints do not force equal valuations: one unit-cost step versus two.
example :
    pathExperience ([⟨0, 2, by decide, 1, 0⟩] : List (LatticeStep ℕ)) ≠
      pathExperience ([⟨0, 1, by decide, 1, 0⟩,
        ⟨1, 2, by decide, 1, 0⟩] : List (LatticeStep ℕ)) := by
  decide
