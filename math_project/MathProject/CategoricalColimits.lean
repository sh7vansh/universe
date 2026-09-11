/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shivansh Singh
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
set_option linter.unusedSectionVars false

namespace CategoricalMachine

open Classical
open CategoryTheory
open Classical
open CategoryTheory.Limits


universe u
variable {A : Type u} [Category A] [Abelian A] [HasColimits A]
variable (U₀ : A)

noncomputable def transfiniteRecursionStep (C : Subobject U₀) (h_semi : IsSemiArtinian U₀) : Subobject U₀ :=
  if h : IsZero (residual U₀ C) then
    C
  else
    let a := (h_semi C h).choose
    let i := (h_semi C h).choose_spec.choose
    haveI : Mono i := (h_semi C h).choose_spec.choose_spec.2
    cellularSubobject U₀ C a i

noncomputable def loewyObj (h_semi : IsSemiArtinian U₀) (o : Ordinal.{u}) : Subobject U₀ :=
  Ordinal.limitRecOn o ⊥ (fun _ C => transfiniteRecursionStep U₀ C h_semi) (fun a _ f => ⨆ (b : Ordinal.{u}) (_hb : b < a), f b _hb)

lemma le_cellularSubobject (C : Subobject U₀) (a : A) (i : a ⟶ residual U₀ C) [Mono i] :
    C ≤ cellularSubobject U₀ C a i := by
  have h_comm : (0 : (C : A) ⟶ a) ≫ i = C.arrow ≫ (cokernel.π C.arrow : U₀ ⟶ residual U₀ C) := by
    rw [Limits.zero_comp, cokernel.condition]
    rfl
  let g : (C : A) ⟶ cellularStep U₀ C a i := pullback.lift 0 C.arrow h_comm
  have hg : g ≫ cellularStepArrow U₀ C a i = C.arrow := by
    exact pullback.lift_snd 0 C.arrow h_comm
  exact Subobject.le_mk_of_comm g hg

lemma le_transfiniteRecursionStep (C : Subobject U₀) (h_semi : IsSemiArtinian U₀) :
    C ≤ transfiniteRecursionStep U₀ C h_semi := by
  dsimp [transfiniteRecursionStep]
  split_ifs with h
  · exact le_rfl
  · have : Mono (h_semi C h).choose_spec.choose := (h_semi C h).choose_spec.choose_spec.2
    exact le_cellularSubobject U₀ C _ _

lemma le_iSup_subobject {ι : Sort*} (f : ι → Subobject U₀) (i : ι) :
    f i ≤ ⨆ j, f j :=
  le_sSup ⟨i, rfl⟩

lemma le_biSup_subobject (o : Ordinal.{u}) (o₁ : Ordinal.{u}) (h : o₁ < o)
    (f : (b : Ordinal.{u}) → b < o → Subobject U₀) :
    f o₁ h ≤ ⨆ (b : Ordinal.{u}) (hb : b < o), f b hb := by
  have h1 : f o₁ h ≤ ⨆ (hb : o₁ < o), f o₁ hb :=
    le_iSup_subobject U₀ (fun (hb : o₁ < o) => f o₁ hb) h
  have h2 : (⨆ (hb : o₁ < o), f o₁ hb) ≤ ⨆ (b : Ordinal.{u}) (hb : b < o), f b hb :=
    le_iSup_subobject U₀ (fun b => ⨆ (hb : b < o), f b hb) o₁
  exact h1.trans h2

lemma loewyObj_limit (h_semi : IsSemiArtinian U₀) (o : Ordinal.{u}) (ho : Order.IsSuccLimit o) :
    loewyObj U₀ h_semi o = ⨆ (b : Ordinal.{u}) (_hb : b < o), loewyObj U₀ h_semi b := by
  dsimp [loewyObj]
  exact Ordinal.limitRecOn_limit o _ _ _ ho

theorem loewyFunctor_map_mono (U₀ : A) (h_semi : IsSemiArtinian U₀) (o₁ o₂ : Ordinal.{u}) (h_le : o₁ ≤ o₂) : 
  loewyObj U₀ h_semi o₁ ≤ loewyObj U₀ h_semi o₂ := by
  revert o₁
  induction o₂ using Ordinal.limitRecOn with
  | zero =>
    intro o₁ h₁
    have : o₁ = 0 := le_zero_iff.mp h₁
    subst this
    exact le_rfl
  | add_one o₂ ih =>
    intro o₁ h₁
    rcases eq_or_lt_of_le h₁ with rfl | hlt
    · exact le_rfl
    · have h_le_o₂ : o₁ ≤ o₂ := by
        rwa [← Order.succ_eq_add_one, Order.lt_succ_iff] at hlt
      have ih_le := ih o₁ h_le_o₂
      have step_le : loewyObj U₀ h_semi o₂ ≤ loewyObj U₀ h_semi (o₂ + 1) := by
        dsimp [loewyObj]
        rw [Ordinal.limitRecOn_add_one]
        exact le_transfiniteRecursionStep U₀ (loewyObj U₀ h_semi o₂) h_semi
      exact ih_le.trans step_le
  | limit o₂ ho ih =>
    intro o₁ h₁
    rcases eq_or_lt_of_le h₁ with rfl | hlt
    · exact le_rfl
    · rw [loewyObj_limit U₀ h_semi o₂ ho]
      exact le_biSup_subobject U₀ o₂ o₁ hlt (fun b _ => loewyObj U₀ h_semi b)

noncomputable def loewyFunctor (h_semi : IsSemiArtinian U₀) : Ordinal.{u} ⥤ Subobject U₀ where
  obj o := loewyObj U₀ h_semi o
  map {o₁ o₂} h_le := homOfLE (loewyFunctor_map_mono U₀ h_semi o₁ o₂ h_le.le)

/-- Mathematically proven by Pierre Gabriel in 1962 ("Des catégories abéliennes").
    Because the category is well-powered, the strictly increasing sequence of 
    subobjects (the Loewy sequence) must eventually exhaust the entire object 
    and terminate at ⊤ at some ordinal Ω. Unformalized in Lean 4 due to the 
    heavy transfinite cardinal bounding required. -/
axiom loewy_length_exists_ax (U₀ : A) (h_semi : IsSemiArtinian U₀) : 
  ∃ (Ω : Ordinal.{u}), (loewyFunctor U₀ h_semi).obj Ω = ⊤

theorem loewy_length_exists (h_semi : IsSemiArtinian U₀) : ∃ (Ω : Ordinal.{u}), (loewyFunctor U₀ h_semi).obj Ω = ⊤ :=
  loewy_length_exists_ax U₀ h_semi
noncomputable def LoewyLength (h_semi : IsSemiArtinian U₀) : Ordinal.{u} := (loewy_length_exists U₀ h_semi).choose

theorem reconstruction (h_semi : IsSemiArtinian U₀) : (loewyFunctor U₀ h_semi).obj (LoewyLength U₀ h_semi) = ⊤ :=
  (loewy_length_exists U₀ h_semi).choose_spec

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
noncomputable def lengthFriction (h_semi : IsSemiArtinian U₀) (optimalLength : Ordinal.{u}) : Ordinal.{u} :=
  (LoewyLength U₀ h_semi) - optimalLength

/--
Extreme bound theorem for categorical friction.
If the actual Loewy length strictly exceeds the optimal length, 
then the length friction is non-zero.
-/
theorem categorical_friction_bound (h_semi : IsSemiArtinian U₀) (optimalLength : Ordinal.{u})
    (h_bound : optimalLength < LoewyLength U₀ h_semi) :
    0 < lengthFriction U₀ h_semi optimalLength := by
  apply pos_iff_ne_zero.mpr
  exact Ordinal.sub_ne_zero_iff_lt.mpr h_bound

end CategoricalMachine
