/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.FunctorialGeometry

/-! # Axiom audit for Loewy depth, branching covers, and generator selection -/

open CategoryTheory Limits FunctorialGeometry

-- Lean audits constants in the statement as well as in the proof. Compare a proof
-- that uses no category operations with the incoming Section 7 interfaces.
private theorem abelianSignatureControl {C : Type*} [Category* C] [Abelian C] : True :=
  True.intro

#print axioms CategoryTheory.Category
#print axioms CategoryTheory.Abelian
#print axioms abelianSignatureControl
#print axioms CategoryTheory.WellPowered
#print axioms IsSemiArtinian
#print axioms CategoryTheory.Subobject.arrow
#print axioms CategoryTheory.Limits.colimit

#print axioms loewySuccessor
#print axioms loewySequence_zero
#print axioms loewySequence_add_one
#print axioms cellularSequence_limit
#print axioms cellularSequence_stabilizes
#print axioms cellular_length_exists
#print axioms reconstruction
#print axioms reconstruction_iso
#print axioms cellularLength_le_of_eq_top
#print axioms cellularSequence_ne_top_of_lt_length
#print axioms cellularSequence_eq_top_iff
#print axioms cellularSequence_strict_before_length
#print axioms cellularSequence_step_exists
#print axioms SingleCellStep.simple_quotient
#print axioms singleCellStep_of_simple
#print axioms singleCellStep_le_next_stage
#print axioms singleCellPathExperience_comp
#print axioms cellular_shortExact
#print axioms cellular_residual_at_top
#print axioms cellular_residual_colimit_vanishes
#print axioms novelty_of_fixedPriorityPhi
#print axioms sieveOutput_eq_top

universe u

variable {A : Type (u + 1)} [Category.{u} A] [Abelian A]
  [HasLimitsOfSize.{u, u} A] [HasColimitsOfSize.{u, u} A] [WellPowered.{u} A]
  (U₀ : A) (h_semi : IsSemiArtinian U₀)

-- A zero object reaches top already at the empty join.
example (hz : IsZero U₀) : cellularLength U₀ h_semi = 0 := by
  apply le_antisymm _ zero_le
  apply cellularLength_le_of_eq_top
  rw [cellularSequence, loewySequence_zero]
  exact (Subobject.subsingleton_of_isZero hz).elim _ _

example (o : Ordinal.{u}) :
    loewySequence U₀ (cellularLength U₀ h_semi + o) = ⊤ :=
  (cellularSequence_eq_top_iff U₀ h_semi _).mpr le_self_add

example : IsZero (colimit (residualDiagram U₀
    (cellularIntervalFunctor U₀ h_semi (cellularLength U₀ h_semi)))) :=
  cellular_residual_colimit_vanishes U₀ h_semi

-- Any supplied simple inclusion yields an edge in the next Loewy layer.
example (o : Ordinal.{u}) (a : A) (i : a ⟶ cokernel (loewySequence U₀ o).arrow)
    [Mono i] (ha : IsSimple a) :
    let D := Subobject.mk (pullback.snd i (cokernel.π (loewySequence U₀ o).arrow))
    SingleCellStep (loewySequence U₀ o) D ∧ D ≤ loewySequence U₀ (o + 1) := by
  have h := singleCellStep_of_simple U₀ _ a i ha
  exact ⟨h, singleCellStep_le_next_stage U₀ o h le_rfl⟩

-- Parallel subobject paths can be compared with one assignment on the covering quiver.
example {C B B' D : Subobject U₀} (h : SingleCellStep C B) (k : SingleCellStep B D)
    (h' : SingleCellStep C B') (k' : SingleCellStep B' D)
    (w : ∀ {X Y : Subobject U₀}, SingleCellStep X Y → TravelExperience) :
    singleCellPathExperience w (h.toPath.append k.toPath) =
      singleCellPathExperience w (h'.toPath.append k'.toPath) ↔ w h * w k = w h' * w k' := by
  simp only [singleCellPathExperience_comp, singleCellPathExperience_edge]

-- Two composable routes, with a single weight function on the four edges.
namespace Diamond

private abbrev Vertex := Bool × Bool

private def viaFirst : SingleCellPath (⊥ : Vertex) ⊤ := by
  have h : SingleCellStep (⊥ : Vertex) (true, false) := Prod.covBy_iff.mpr (by decide)
  have k : SingleCellStep (true, false) (⊤ : Vertex) := Prod.covBy_iff.mpr (by decide)
  exact h.toPath.append k.toPath

private def viaSecond : SingleCellPath (⊥ : Vertex) ⊤ := by
  have h : SingleCellStep (⊥ : Vertex) (false, true) := Prod.covBy_iff.mpr (by decide)
  have k : SingleCellStep (false, true) (⊤ : Vertex) := Prod.covBy_iff.mpr (by decide)
  exact h.toPath.append k.toPath

private def weight {X Y : Vertex} (_ : SingleCellStep X Y) : TravelExperience :=
  if X = (true, false) then ⟨2, ⟨-1⟩⟩ else ⟨1, ⟨1⟩⟩

theorem route_values :
    singleCellPathExperience weight viaFirst = ⟨3, ⟨0⟩⟩ ∧
    singleCellPathExperience weight viaSecond = ⟨2, ⟨2⟩⟩ := ⟨rfl, rfl⟩

#print axioms route_values

end Diamond
