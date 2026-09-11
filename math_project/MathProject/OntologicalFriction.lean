/-
Copyright (c) 2024 MathProject Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MathProject Authors
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs

/-!
# OntologicalFriction

This module implements OntologicalFriction.
-/

set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

namespace OntologicalFriction

variable {U : Type} [Fintype U]
variable (cl : Set U → Set U)

/-- A set is a generating set if its closure covers the universe. -/
def IsGeneratingSet (S : Set U) : Prop :=
  cl S = Set.univ

/-- An optimal generating set minimizes cardinality. -/
def IsOptimalGenerator (S : Set U) : Prop :=
  IsGeneratingSet cl S ∧ ∀ T, IsGeneratingSet cl T → S.toFinite.toFinset.card ≤ T.toFinite.toFinset.card

/-- The approximation ratio (Friction 1) compares the sieve's output to the optimal size. -/
noncomputable def cardinalityBloat (sieve_output : Set U) (opt : Set U) 
    (_h_opt : IsOptimalGenerator cl opt) : ℚ :=
  (sieve_output.toFinite.toFinset.card : ℚ) / (opt.toFinite.toFinset.card : ℚ)

/-- Search Work (Friction 2) represents the discard rate W. -/
noncomputable def searchWork (k : ℕ) (sieve_output : Set U) : ℚ :=
  let b_omega := sieve_output.toFinite.toFinset.card
  if k = 0 then (0 : ℚ) else ((k - b_omega : ℕ) : ℚ) / (k : ℚ)

end OntologicalFriction
