/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Authors: Shivansh Singh
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import MathProject.CategoricalMachine

/-!
# YonedaExtension

This module proves that every cellular pullback step in `CategoricalMachine`
forms a short exact sequence:
`0 ⟶ C ⟶ cellularStep U₀ C a i ⟶ a ⟶ 0`
classifying a length-1 Yoneda extension class `ξ ∈ Ext¹(a, C)`.
-/

set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.style.header false

namespace CategoricalMachine

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (U₀ : A)

section

variable (C : Subobject U₀) (a : A) (i : a ⟶ cokernel C.arrow) [Mono i]

lemma cellular_comm : (0 : (C : A) ⟶ a) ≫ i = C.arrow ≫ cokernel.π C.arrow := by
  rw [Limits.zero_comp, cokernel.condition]

/-- Canonical inclusion morphism from subobject `C` into the cellular pullback object. -/
noncomputable def cellularInclusion : (C : A) ⟶ pullback i (cokernel.π C.arrow) :=
  pullback.lift 0 C.arrow (cellular_comm U₀ C a i)

/-- Canonical projection morphism from the cellular pullback object onto simple layer `a`. -/
noncomputable def cellularProjection : pullback i (cokernel.π C.arrow) ⟶ a :=
  pullback.fst i (cokernel.π C.arrow)

@[simp]
lemma cellularInclusion_fst :
    cellularInclusion U₀ C a i ≫ pullback.fst i (cokernel.π C.arrow) = 0 := by
  dsimp [cellularInclusion]
  exact pullback.lift_fst 0 C.arrow (cellular_comm U₀ C a i)

@[simp]
lemma cellularInclusion_snd :
    cellularInclusion U₀ C a i ≫ pullback.snd i (cokernel.π C.arrow) = C.arrow := by
  dsimp [cellularInclusion]
  exact pullback.lift_snd 0 C.arrow (cellular_comm U₀ C a i)

lemma cellularInclusion_comp_projection :
    cellularInclusion U₀ C a i ≫ cellularProjection U₀ C a i = 0 :=
  cellularInclusion_fst U₀ C a i

instance : Mono (cellularInclusion U₀ C a i) := by
  have hg := cellularInclusion_snd U₀ C a i
  have : Mono C.arrow := C.arrow_mono
  exact mono_of_mono_fac hg

instance : Epi (cellularProjection U₀ C a i) := by
  dsimp [cellularProjection]
  infer_instance

/-- The short complex `C ⟶ pullback i (cokernel.π C.arrow) ⟶ a`. -/
noncomputable def cellularShortComplex : ShortComplex A :=
  ShortComplex.mk (cellularInclusion U₀ C a i) (cellularProjection U₀ C a i)
    (cellularInclusion_comp_projection U₀ C a i)

lemma coker_snd_comp_coker (s : KernelFork (cellularProjection U₀ C a i)) :
    (s.ι ≫ pullback.snd i (cokernel.π C.arrow)) ≫ cokernel.π C.arrow = 0 := by
  calc
    (s.ι ≫ pullback.snd i (cokernel.π C.arrow)) ≫ cokernel.π C.arrow
      = s.ι ≫ (pullback.snd i (cokernel.π C.arrow) ≫ cokernel.π C.arrow) := by rw [Category.assoc]
    _ = s.ι ≫ (pullback.fst i (cokernel.π C.arrow) ≫ i) := by rw [pullback.condition]
    _ = (s.ι ≫ pullback.fst i (cokernel.π C.arrow)) ≫ i := by rw [← Category.assoc]
    _ = (s.ι ≫ cellularProjection U₀ C a i) ≫ i := rfl
    _ = 0 ≫ i := by rw [KernelFork.condition s]
    _ = 0 := zero_comp

noncomputable def cellularLift (s : KernelFork (cellularProjection U₀ C a i))
    (h_coker_isLimit : IsLimit (KernelFork.ofι C.arrow (cokernel.condition C.arrow))) :
    s.pt ⟶ (C : A) :=
  h_coker_isLimit.lift (KernelFork.ofι (s.ι ≫ pullback.snd i (cokernel.π C.arrow)) (coker_snd_comp_coker U₀ C a i s))

lemma cellularLift_fac (s : KernelFork (cellularProjection U₀ C a i))
    (h_coker_isLimit : IsLimit (KernelFork.ofι C.arrow (cokernel.condition C.arrow))) :
    cellularLift U₀ C a i s h_coker_isLimit ≫ cellularInclusion U₀ C a i = s.ι := by
  have hu : cellularLift U₀ C a i s h_coker_isLimit ≫ C.arrow = s.ι ≫ pullback.snd i (cokernel.π C.arrow) :=
    h_coker_isLimit.fac (KernelFork.ofι (s.ι ≫ pullback.snd i (cokernel.π C.arrow)) (coker_snd_comp_coker U₀ C a i s)) WalkingParallelPair.zero
  apply pullback.hom_ext
  · simp only [Category.assoc, cellularInclusion_fst, comp_zero]
    exact (KernelFork.condition s).symm
  · simp only [Category.assoc, cellularInclusion_snd]
    exact hu

lemma cellularLift_uniq (s : KernelFork (cellularProjection U₀ C a i))
    (h_coker_isLimit : IsLimit (KernelFork.ofι C.arrow (cokernel.condition C.arrow)))
    (m : s.pt ⟶ (C : A)) (hm : m ≫ cellularInclusion U₀ C a i = s.ι) :
    m = cellularLift U₀ C a i s h_coker_isLimit := by
  have hm_coker : m ≫ C.arrow = s.ι ≫ pullback.snd i (cokernel.π C.arrow) := by
    calc
      m ≫ C.arrow = m ≫ (cellularInclusion U₀ C a i ≫ pullback.snd i (cokernel.π C.arrow)) := by rw [cellularInclusion_snd]
      _ = (m ≫ cellularInclusion U₀ C a i) ≫ pullback.snd i (cokernel.π C.arrow) := by rw [Category.assoc]
      _ = s.ι ≫ pullback.snd i (cokernel.π C.arrow) := by rw [hm]
  have hu : cellularLift U₀ C a i s h_coker_isLimit ≫ C.arrow = s.ι ≫ pullback.snd i (cokernel.π C.arrow) :=
    h_coker_isLimit.fac (KernelFork.ofι (s.ι ≫ pullback.snd i (cokernel.π C.arrow)) (coker_snd_comp_coker U₀ C a i s)) WalkingParallelPair.zero
  have h_eq : m ≫ C.arrow = cellularLift U₀ C a i s h_coker_isLimit ≫ C.arrow := by rw [hm_coker, hu]
  have : Mono C.arrow := C.arrow_mono
  exact (cancel_mono C.arrow).mp h_eq

/-- The kernel fork of the cellular projection is a limit cone, showing that the kernel
    of `cellularProjection` is canonically isomorphic to `C`. -/
noncomputable def isLimitCellularKernelFork :
    IsLimit (KernelFork.ofι (cellularInclusion U₀ C a i) (cellularInclusion_comp_projection U₀ C a i)) := by
  have h_coker_isLimit : IsLimit (KernelFork.ofι C.arrow (cokernel.condition C.arrow)) :=
    Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ (cokernel.π C.arrow) (cokernel.condition C.arrow))
      (cokernelIsCokernel C.arrow)
  exact Fork.IsLimit.mk _
    (fun s => cellularLift U₀ C a i s h_coker_isLimit)
    (fun s => cellularLift_fac U₀ C a i s h_coker_isLimit)
    (fun s m hm => cellularLift_uniq U₀ C a i s h_coker_isLimit m hm)

/-- The sequence `0 ⟶ C ⟶ pullback ⟶ a ⟶ 0` is exact. -/
theorem cellular_exact :
    (cellularShortComplex U₀ C a i).Exact :=
  ShortComplex.exact_of_f_is_kernel (cellularShortComplex U₀ C a i) (isLimitCellularKernelFork U₀ C a i)

instance : Mono (cellularShortComplex U₀ C a i).f := by
  dsimp [cellularShortComplex]
  infer_instance

instance : Epi (cellularShortComplex U₀ C a i).g := by
  dsimp [cellularShortComplex]
  infer_instance

/-- Main Yoneda Extension Theorem: Every cellular step is a Short Exact Sequence,
    classifying a length-1 Yoneda extension class `ξ ∈ Ext¹(a, C)`. -/
theorem cellular_shortExact :
    (cellularShortComplex U₀ C a i).ShortExact where
  exact := cellular_exact U₀ C a i

end

end CategoricalMachine
