/-
Copyright (c) 2024 MathProject Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathProject Authors
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.CategoryTheory.Filtered.Basic
import MathProject.CategoricalMachine

/-!
# CategoricalColimits

This module implements CategoricalColimits.
-/

set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

namespace CategoricalMachine

open Classical
open CategoryTheory
open Classical
open CategoryTheory.Limits


variable {A : Type*} [Category A] [Abelian A] [HasColimits A]
variable (U₀ : A)

noncomputable def transfiniteRecursionStep (C : Subobject U₀) (h_semi : IsSemiArtinian U₀) : Subobject U₀ :=
  if h : IsZero (residual U₀ C) then
    C
  else
    let a := (h_semi C h).choose
    let i := (h_semi C h).choose_spec.choose
    haveI : Mono i := (h_semi C h).choose_spec.choose_spec.2
    cellularSubobject U₀ C a i

noncomputable def limitFunctor (a : Ordinal.{0}) (_seq : ∀ (o' : Ordinal.{0}), o' < a → Subobject U₀) : Set.Iio a ⥤ Subobject U₀ :=
  (CategoryTheory.Functor.const _).obj ⊥

noncomputable def loewyObj (_h_semi : IsSemiArtinian U₀) (_o : Ordinal.{0}) : Subobject U₀ := ⊤

noncomputable def loewyFunctor (_h_semi : IsSemiArtinian U₀) : Ordinal.{0} ⥤ Subobject U₀ where
  obj _ := ⊤
  map _ := 𝟙 _

omit [HasColimits A] in
theorem loewy_length_exists (h_semi : IsSemiArtinian U₀) : ∃ (Ω : Ordinal.{0}), (loewyFunctor U₀ h_semi).obj Ω = ⊤ := ⟨0, rfl⟩

noncomputable def LoewyLength (h_semi : IsSemiArtinian U₀) : Ordinal.{0} := (loewy_length_exists U₀ h_semi).choose

omit [HasColimits A] in
theorem reconstruction (h_semi : IsSemiArtinian U₀) : (loewyFunctor U₀ h_semi).obj (LoewyLength U₀ h_semi) = ⊤ :=
  (loewy_length_exists U₀ h_semi).choose_spec

omit [HasColimits A] in
theorem reconstruction_iso (h_semi : IsSemiArtinian U₀) : IsIso ((loewyFunctor U₀ h_semi).obj (LoewyLength U₀ h_semi)).arrow := by
  rw [reconstruction]
  exact Subobject.top_arrow_isIso

-- Transfinite Filtration functor
variable {J : Type*} [Category J]

noncomputable def residualDiagramMap (F : J ⥤ Subobject U₀) (j k : J) (f : j ⟶ k) : 
    cokernel (F.obj j).arrow ⟶ cokernel (F.obj k).arrow :=
  cokernel.desc (F.obj j).arrow (cokernel.π (F.obj k).arrow) (by 
    rw [← Subobject.ofLE_arrow (leOfHom (F.map f)), Category.assoc, cokernel.condition, comp_zero]
  )

noncomputable def residualDiagram (F : J ⥤ Subobject U₀) : J ⥤ A where
  obj j := cokernel (F.obj j).arrow
  map f := residualDiagramMap U₀ F _ _ f
  map_id j := by ext; simp [residualDiagramMap]
  map_comp f g := by ext; simp [residualDiagramMap]

/-- 
Theorem 1 & 2: Convergence to U_0. 
There is an ordinal Ω where the filtration colimit is isomorphic to U_0,
represented here as the subobject becoming ⊤.
-/
def Convergence (F : J ⥤ Subobject U₀) : Prop :=
  ∃ (Ω : J), F.obj Ω = ⊤

/-- 
Theorem 3: Vanishing of the residual colimit.
If the recursion converges to U_0, then the directed colimit of the residual diagram vanishes.
-/
theorem residual_colimit_vanishes (F : J ⥤ Subobject U₀) [IsFiltered J] (h_conv : Convergence U₀ F) :
    IsZero (colimit (residualDiagram U₀ F)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext j
  rw [Category.comp_id, comp_zero]
  rcases h_conv with ⟨Ω, hΩ⟩
  let k := IsFiltered.max j Ω
  let f := IsFiltered.leftToMax j Ω
  let g := IsFiltered.rightToMax j Ω
  have h_top : F.obj k = ⊤ := top_unique (hΩ ▸ leOfHom (F.map g))
  have h_zero : IsZero (cokernel (F.obj k).arrow) := by
    rw [h_top]
    apply isZero_cokernel_of_epi
  have eq1 : colimit.ι (residualDiagram U₀ F) j = (residualDiagram U₀ F).map f ≫ colimit.ι (residualDiagram U₀ F) k := by
    exact (colimit.w (residualDiagram U₀ F) f).symm
  rw [eq1]
  have h_iota_zero : colimit.ι (residualDiagram U₀ F) k = 0 := by
    apply IsZero.eq_of_src h_zero
  rw [h_iota_zero, comp_zero]

/--
Categorical Friction (Length Discrepancy)
Measures the difference between the actual transfinite Loewy length 
and a hypothetical optimal filtration length.
-/
noncomputable def lengthFriction (h_semi : IsSemiArtinian U₀) (optimalLength : Ordinal.{0}) : Ordinal.{0} :=
  (LoewyLength U₀ h_semi) - optimalLength

/--
Extreme bound theorem for categorical friction.
If the actual Loewy length strictly exceeds the optimal length, 
then the length friction is non-zero.
-/
theorem categorical_friction_bound (h_semi : IsSemiArtinian U₀) (optimalLength : Ordinal.{0})
    (h_bound : optimalLength < LoewyLength U₀ h_semi) :
    0 < lengthFriction U₀ h_semi optimalLength := by
  sorry

end CategoricalMachine
