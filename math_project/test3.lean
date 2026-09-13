import Mathlib.Order.Cover
import Mathlib.Order.Atoms
import Mathlib.Order.CompleteLattice.Basic

variable {L : Type*} [CompleteLattice L]

def MacLaneSteinitz : Prop :=
  ∀ a b x : L, IsAtom a → IsAtom b → a ≤ x ⊔ b → ¬(a ≤ x) → b ≤ x ⊔ a

