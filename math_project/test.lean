import Mathlib.Order.Cover
import Mathlib.Order.CompleteLattice.Basic

variable {L : Type*} [CompleteLattice L]

def MacLaneSteinitz : Prop :=
  ∀ a b x : L, a ≤ x ⊔ b → ¬(a ≤ x) → b ≤ x ⊔ a

#check MacLaneSteinitz
#check @MacLaneSteinitz

def GeometricFriction : Prop :=
  ¬ @MacLaneSteinitz L _

