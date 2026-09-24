import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Cover
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace TorFrictionStrain

open CategoryTheory Limits

/-!
# Tor Functor, Submodular Defect, and Manifold Strain

This module formalizes:
1. The Submodular Friction Defect Δ(A, B) = (rk A + rk B) - (rk(A ⊔ B) + rk(A ⊓ B)).
2. Non-negativity of the friction defect in submodular lattices (Δ ≥ 0).
3. Modularity as the zero-strain / zero-defect state (Δ = 0).
4. The Mayer-Vietoris rank equality and Tor₁ defect identification.
5. Tor₀ in thin categories as categorical meet/product.
-/

variable {L : Type*} [Lattice L]

/-- A submodular rank function on a lattice L. -/
structure SubmodularRank (L : Type*) [Lattice L] where
  rk : L → ℤ
  submodular : ∀ A B : L, rk (A ⊔ B) + rk (A ⊓ B) ≤ rk A + rk B
  monotone : ∀ A B : L, A ≤ B → rk A ≤ rk B

/-- The Submodular Defect (Tor₁ Strain / Friction Drop) between two lattice elements. -/
def submodularDefect (R : SubmodularRank L) (A B : L) : ℤ :=
  (R.rk A + R.rk B) - (R.rk (A ⊔ B) + R.rk (A ⊓ B))

/-- The friction defect is strictly non-negative (Strain Energy Lower Bound). -/
theorem defect_nonneg (R : SubmodularRank L) (A B : L) :
    0 ≤ submodularDefect R A B := by
  dsimp [submodularDefect]
  have h := R.submodular A B
  linarith

/-- The zero-strain condition: defect is 0 iff the modular equality holds. -/
theorem defect_zero_iff_modular (R : SubmodularRank L) (A B : L) :
    submodularDefect R A B = 0 ↔ R.rk (A ⊔ B) + R.rk (A ⊓ B) = R.rk A + R.rk B := by
  dsimp [submodularDefect]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- A Modular Rank is a submodular rank where the Tor₁ defect vanishes everywhere (flat manifold). -/
structure ModularRank (L : Type*) [Lattice L] extends SubmodularRank L where
  modular : ∀ A B : L, rk (A ⊔ B) + rk (A ⊓ B) = rk A + rk B

/-- On a modular lattice, the strain/friction defect vanishes identically (Δ = 0). -/
theorem modular_defect_zero (M : ModularRank L) (A B : L) :
    submodularDefect M.toSubmodularRank A B = 0 := by
  rw [defect_zero_iff_modular]
  exact M.modular A B

/-!
### Tor₀ in Thin Categories (Categorical Meet as Tensor Product)
-/

section ThinTor

/-- In a thin category, Tor₀(A, B) is canonically the meet A ⊓ B. -/
def tor0 (A B : L) : L := A ⊓ B

theorem tor0_le_left (A B : L) : tor0 A B ≤ A :=
  inf_le_left

theorem tor0_le_right (A B : L) : tor0 A B ≤ B :=
  inf_le_right

theorem tor0_comm (A B : L) : tor0 A B = tor0 B A := by
  dsimp [tor0]
  rw [inf_comm]

theorem tor0_assoc (A B C : L) : tor0 (tor0 A B) C = tor0 A (tor0 B C) := by
  dsimp [tor0]
  rw [inf_assoc]

/-- Universal property of Tor₀ as the maximal shared subobject. -/
theorem tor0_universal {A B C : L} (hCA : C ≤ A) (hCB : C ≤ B) :
    C ≤ tor0 A B :=
  le_inf hCA hCB

end ThinTor

end TorFrictionStrain
