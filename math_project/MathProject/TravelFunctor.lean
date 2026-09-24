/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shivansh Singh
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Cover
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace TravelFunctor

/-!
# The Unified Travel Functor: Action (Friction Cost) + Holonomy (Unipotent Transport)

This module formalizes:
1. The 2x2 Unipotent Shear Group (Matrix Holonomy).
2. The Travel State: A pair (action, transport) where action adds and transport multiplies.
3. The Functoriality laws: identity preservation and composition law.
4. The Action lower bound: travel effort is strictly positive for non-trivial paths.
-/

/-- A 2x2 upper-triangular unipotent matrix [[1, e], [0, 1]] representing the algebraic shear. -/
@[ext]
structure Unipotent2 where
  e : ℤ
  deriving DecidableEq, Repr

namespace Unipotent2

def id : Unipotent2 := ⟨0⟩

/-- Matrix multiplication of two unipotent shears:
    [[1, e1], [0, 1]] * [[1, e2], [0, 1]] = [[1, e1 + e2], [0, 1]] -/
def mul (m1 m2 : Unipotent2) : Unipotent2 :=
  ⟨m1.e + m2.e⟩

instance : One Unipotent2 := ⟨id⟩
instance : Mul Unipotent2 := ⟨mul⟩

@[simp] theorem id_e : (1 : Unipotent2).e = 0 := rfl
@[simp] theorem mul_e (m1 m2 : Unipotent2) : (m1 * m2).e = m1.e + m2.e := rfl

theorem mul_assoc (a b c : Unipotent2) : (a * b) * c = a * (b * c) := by
  rcases a with ⟨a1⟩
  rcases b with ⟨b1⟩
  rcases c with ⟨c1⟩
  ext
  change (a1 + b1) + c1 = a1 + (b1 + c1)
  omega

theorem one_mul (a : Unipotent2) : 1 * a = a := by
  rcases a with ⟨a1⟩
  ext
  change 0 + a1 = a1
  omega

theorem mul_one (a : Unipotent2) : a * 1 = a := by
  rcases a with ⟨a1⟩
  ext
  change a1 + 0 = a1
  omega

end Unipotent2

open Unipotent2

/-- The Travel State: (Action, Transport)
    - action : The accumulated Lagrangian friction/effort (≥ 0)
    - transport : The unipotent geometric shear felt along the edge -/
@[ext]
structure TravelExperience where
  action : ℕ
  transport : Unipotent2
  deriving DecidableEq, Repr

namespace TravelExperience

/-- Standing still (Identity travel): Zero effort, zero shear. -/
def id : TravelExperience := ⟨0, 1⟩

/-- Sequential travel composition:
    - Efforts add: S_total = S1 + S2
    - Transports multiply: T_total = T1 * T2 -/
def comp (t1 t2 : TravelExperience) : TravelExperience :=
  ⟨t1.action + t2.action, t1.transport * t2.transport⟩

instance : One TravelExperience := ⟨id⟩
instance : Mul TravelExperience := ⟨comp⟩

@[simp] theorem id_action : (1 : TravelExperience).action = 0 := rfl
@[simp] theorem id_transport : (1 : TravelExperience).transport = 1 := rfl

@[simp] theorem comp_action (t1 t2 : TravelExperience) :
    (t1 * t2).action = t1.action + t2.action := rfl

@[simp] theorem comp_transport (t1 t2 : TravelExperience) :
    (t1 * t2).transport = t1.transport * t2.transport := rfl

/-- Travel composition is associative. -/
theorem comp_assoc (a b c : TravelExperience) : (a * b) * c = a * (b * c) := by
  rcases a with ⟨a1, ⟨a2⟩⟩
  rcases b with ⟨b1, ⟨b2⟩⟩
  rcases c with ⟨c1, ⟨c2⟩⟩
  ext
  · change (a1 + b1) + c1 = a1 + (b1 + c1)
    omega
  · change (a2 + b2) + c2 = a2 + (b2 + c2)
    omega

/-- Standing still is the left identity of travel. -/
theorem one_comp (a : TravelExperience) : 1 * a = a := by
  rcases a with ⟨a1, ⟨a2⟩⟩
  ext
  · change 0 + a1 = a1
    omega
  · change 0 + a2 = a2
    omega

/-- Standing still is the right identity of travel. -/
theorem comp_one (a : TravelExperience) : a * 1 = a := by
  rcases a with ⟨a1, ⟨a2⟩⟩
  ext
  · change a1 + 0 = a1
    omega
  · change a2 + 0 = a2
    omega

end TravelExperience

open TravelExperience

/-!
### The Travel Functor on Lattice Morphisms
-/

variable {L : Type*} [PartialOrder L]

/-- An elementary step along a covering edge in the lattice. -/
structure LatticeStep (L : Type*) [PartialOrder L] where
  source : L
  target : L
  le : source ≤ target
  friction_cost : ℕ
  ext_class : ℤ

/-- The Travel Functor evaluation on an elementary lattice step. -/
def stepExperience (s : LatticeStep L) : TravelExperience :=
  ⟨s.friction_cost, ⟨s.ext_class⟩⟩

/-- The total travel effort along a path is additive. -/
theorem path_action_additive (s1 s2 : LatticeStep L) :
    (stepExperience s1 * stepExperience s2).action = s1.friction_cost + s2.friction_cost :=
  rfl

/-- The total geometric shear along a path is additive in Ext¹. -/
theorem path_shear_additive (s1 s2 : LatticeStep L) :
    (stepExperience s1 * stepExperience s2).transport.e = s1.ext_class + s2.ext_class :=
  rfl

/-- Non-trivial travel strictly increases accumulated action (No Free Travel). -/
theorem action_strictly_increases (t : TravelExperience) (s : LatticeStep L) (hcost : 0 < s.friction_cost) :
    t.action < (t * stepExperience s).action := by
  dsimp [stepExperience]
  linarith

end TravelFunctor
