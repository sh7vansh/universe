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
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# CategoricalMachine

This module implements CategoricalMachine.
-/

set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

namespace CategoricalMachine

open CategoryTheory
open CategoryTheory.Limits

variable {A : Type*} [Category A] [Abelian A]

def IsSimple (X : A) : Prop :=
  ¬ IsZero X ∧ ∀ (Y : Subobject X), Y = ⊥ ∨ Y = ⊤

variable (U₀ : A)

noncomputable def residual (C : Subobject U₀) : A :=
  cokernel C.arrow

def IsSemiArtinian (U₀ : A) : Prop :=
  ∀ (C : Subobject U₀), ¬ IsZero (residual U₀ C) → 
    ∃ (a : A) (i : a ⟶ residual U₀ C), IsSimple a ∧ Mono i

noncomputable def cellularStep (C : Subobject U₀) (a : A) (i : a ⟶ residual U₀ C) [Mono i] : A :=
  pullback i (cokernel.π C.arrow)

noncomputable def cellularStepArrow (C : Subobject U₀) (a : A) (i : a ⟶ residual U₀ C) [Mono i] : cellularStep U₀ C a i ⟶ U₀ :=
  pullback.snd i (cokernel.π C.arrow)

instance cellularStep_is_mono (C : Subobject U₀) (a : A) (i : a ⟶ residual U₀ C) [Mono i] : Mono (cellularStepArrow U₀ C a i) := by
  dsimp [cellularStepArrow]
  exact pullback.snd_of_mono

noncomputable def cellularSubobject (C : Subobject U₀) (a : A) (i : a ⟶ residual U₀ C) [Mono i] : Subobject U₀ :=
  Subobject.mk (cellularStepArrow U₀ C a i)

end CategoricalMachine
