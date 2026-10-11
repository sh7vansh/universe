/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.FunctorialGeometry

/-! # Axiom audit and endpoint checks for order-continuous cellular filtrations -/

open CategoryTheory Limits FunctorialGeometry

#print axioms cellularSequence_limit
#print axioms cellular_length_exists
#print axioms reconstruction
#print axioms cellularLength_le_of_eq_top
#print axioms cellularSequence_ne_top_of_lt_length
#print axioms cellularSequence_eq_top_iff
#print axioms cellularSequence_strict_before_length
#print axioms cellularSequence_step_exists
#print axioms cellular_shortExact
#print axioms cellular_residual_colimit_vanishes
#print axioms novelty_of_fixedPriorityPhi
#print axioms sieveOutput_eq_top

universe u

variable {A : Type (u + 1)} [Category.{u} A] [Abelian A]
  [HasLimitsOfSize.{u, u} A] [HasColimitsOfSize.{u, u} A] [WellPowered.{u} A]
  (U₀ : A) (h_semi : IsSemiArtinian U₀)

-- A sequence already at top in its base stage has length zero, with no padded tail.
example (hzero : cellularSequence U₀ h_semi 0 = ⊤) :
    cellularLength U₀ h_semi = 0 :=
  le_antisymm (cellularLength_le_of_eq_top U₀ h_semi 0 hzero) zero_le

-- The endpoint remains top at every later ordinal.
example (o : Ordinal.{u}) :
    cellularSequence U₀ h_semi (cellularLength U₀ h_semi + o) = ⊤ :=
  (cellularSequence_eq_top_iff U₀ h_semi _).mpr le_self_add

-- Every successor before the endpoint has a chosen simple cell.
example (o : Ordinal.{u}) (ho : o < cellularLength U₀ h_semi) :
    ∃ (a : A) (i : a ⟶ residual U₀ (cellularSequence U₀ h_semi o)),
      IsSimple a ∧ Mono i := by
  obtain ⟨a, i, hi, ha, _⟩ := cellularSequence_step_exists U₀ h_semi o
    (cellularSequence_ne_top_of_lt_length U₀ h_semi o ho)
  exact ⟨a, i, ha, hi⟩
