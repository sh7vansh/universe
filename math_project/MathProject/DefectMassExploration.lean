import MathProject.FunctorialGeometry

/-!
# Algebraic constraints for a defect-as-mass thought experiment

These are consequences of the existing definitions, not assertions about physical
mass or gravity. In particular, potential-difference travel has no dependence on
the intermediate route. Quantum dynamics is investigated separately in
`new_frontiers/experiments/defect_universe/run.py`.
-/

namespace DefectMassExploration

open FunctorialGeometry

variable {L : Type*} [Lattice L]

theorem defect_symm (R : SubmodularRank L) (A B : L) :
    submodularDefect R A B = submodularDefect R B A := by
  simp only [submodularDefect, sup_comm A B, inf_comm A B]
  ring

/-- A directed order step cannot itself have nonzero endpoint defect. -/
theorem defect_of_le (R : SubmodularRank L) {A B : L} (h : A ≤ B) :
    submodularDefect R A B = 0 := by
  simp only [submodularDefect, sup_eq_right.mpr h, inf_eq_left.mpr h]
  ring

/-- Relabelling an element by a lattice automorphism does not change its defect,
provided that the valuation is invariant too. -/
theorem defect_orderIso (R : SubmodularRank L) (e : L ≃o L)
    (hr : ∀ X, R.rk (e X) = R.rk X) (A B : L) :
    submodularDefect R (e A) (e B) = submodularDefect R A B := by
  simp only [submodularDefect, ← e.map_sup, ← e.map_inf, hr]

/-- Difference between a modular size valuation and a submodular rank.
For an edge-set lattice with graphic rank, this is the cycle count (nullity).
Nonnegativity needs size/rank assumptions and is not claimed for arbitrary N, R. -/
def structuralMass (N : ModularRank L) (R : SubmodularRank L) (A : L) : ℤ :=
  N.rk A - R.rk A

theorem defect_eq_mass_excess (N : ModularRank L) (R : SubmodularRank L)
    (A B : L) :
    submodularDefect R A B =
      structuralMass N R (A ⊔ B) + structuralMass N R (A ⊓ B) -
        structuralMass N R A - structuralMass N R B := by
  have h := N.modular A B
  dsimp [submodularDefect, structuralMass]
  linarith

/-- Adding a massless component with massless intersection converts pair defect
to an increase of intrinsic structural mass. -/
theorem defect_eq_mass_increment (N : ModularRank L) (R : SubmodularRank L)
    (A B : L) (hB : structuralMass N R B = 0)
    (hmeet : structuralMass N R (A ⊓ B) = 0) :
    submodularDefect R A B = structuralMass N R (A ⊔ B) - structuralMass N R A := by
  rw [defect_eq_mass_excess N R A B, hB, hmeet]
  ring

/-- This rules out a nonzero intrinsic mass determined by EVERY join
decomposition without restricting which decompositions are admissible. -/
theorem unrestricted_join_mass_zero [OrderBot L] (R : SubmodularRank L)
    (mass : L → ℤ)
    (h : ∀ A B, mass (A ⊔ B) = submodularDefect R A B) (A : L) :
    mass A = 0 := by
  have hh := h A ⊥
  rw [sup_bot_eq, defect_symm R A ⊥, defect_of_le R bot_le] at hh
  exact hh

/-- An integer-valued potential can define an additive travel label. -/
def potentialTravel (mass : L → ℤ) (A B : L) : ℤ := mass B - mass A

omit [Lattice L] in
theorem potentialTravel_comp (mass : L → ℤ) (A B C : L) :
    potentialTravel mass A B + potentialTravel mass B C = potentialTravel mass A C := by
  dsimp [potentialTravel]
  ring

omit [Lattice L] in
/-- Every chain of potential differences telescopes, regardless of its interior.
It cannot alone distinguish two histories having the same endpoints. -/
theorem potentialTravel_telescope (mass : L → ℤ) (x : ℕ → L) (n : ℕ) :
    (∑ i ∈ Finset.range n, potentialTravel mass (x i) (x (i + 1))) =
      mass (x n) - mass (x 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    dsimp [potentialTravel]
    ring

omit [Lattice L] in
/-- If all individual phase labels are mass increments, the old additive
transport also forgets the interior of the construction history. -/
theorem equal_endpoint_travel (mass : L → ℤ) (x y : ℕ → L) (n m : ℕ)
    (hstart : x 0 = y 0) (hend : x n = y m) :
    (∑ i ∈ Finset.range n, potentialTravel mass (x i) (x (i + 1))) =
      ∑ i ∈ Finset.range m, potentialTravel mass (y i) (y (i + 1)) := by
  rw [potentialTravel_telescope, potentialTravel_telescope, hstart, hend]

end DefectMassExploration

#print axioms DefectMassExploration.defect_of_le
#print axioms DefectMassExploration.defect_orderIso
#print axioms DefectMassExploration.defect_eq_mass_excess
#print axioms DefectMassExploration.defect_eq_mass_increment
#print axioms DefectMassExploration.unrestricted_join_mass_zero
#print axioms DefectMassExploration.potentialTravel_telescope
#print axioms DefectMassExploration.equal_endpoint_travel
