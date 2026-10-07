import MathProject.DefectMassExploration
import Mathlib.Data.Complex.Basic

/-!
# Can composition select a nontrivial defect phase?

The obstruction here concerns decorating the binary lattice join itself.
It does not prohibit additive phase labels on retained histories, nor the
separate unitary collision rule in the quantum-walk experiments.
-/

namespace TravelRuleSelection

open FunctorialGeometry DefectMassExploration

variable {L : Type*} [Lattice L]

/-- A normalized scalar phase on pair defects cannot decorate every lattice
join associatively unless every realized defect receives the identity phase.
Choose the third input to be the join of the first two. -/
theorem associative_join_phase_trivial {P : Type*} [Monoid P]
    (R : SubmodularRank L) (phase : ℤ → P) (hzero : phase 0 = 1)
    (hassoc : ∀ A B C : L,
      phase (submodularDefect R A B) * phase (submodularDefect R (A ⊔ B) C) =
      phase (submodularDefect R B C) * phase (submodularDefect R A (B ⊔ C)))
    (A B : L) : phase (submodularDefect R A B) = 1 := by
  have h := hassoc A B (A ⊔ B)
  have hself : submodularDefect R (A ⊔ B) (A ⊔ B) = 0 :=
    defect_of_le R le_rfl
  have hright : submodularDefect R B (A ⊔ B) = 0 :=
    defect_of_le R le_sup_right
  have hleft : submodularDefect R A (A ⊔ B) = 0 :=
    defect_of_le R le_sup_left
  rw [hself, hright, sup_eq_right.mpr (show B ≤ A ⊔ B from le_sup_right),
    hleft, hzero, mul_one, one_mul] at h
  exact h

/-- The same obstruction applies if the binary operation is meet, the paper's
`meetInteraction`, and comparable inputs receive identity phase. -/
theorem associative_meet_phase_trivial {P : Type*} [Monoid P]
    (R : SubmodularRank L) (phase : ℤ → P) (hzero : phase 0 = 1)
    (hassoc : ∀ A B C : L,
      phase (submodularDefect R A B) * phase (submodularDefect R (A ⊓ B) C) =
      phase (submodularDefect R B C) * phase (submodularDefect R A (B ⊓ C)))
    (A B : L) : phase (submodularDefect R A B) = 1 := by
  have h := hassoc A B (A ⊓ B)
  have hself : submodularDefect R (A ⊓ B) (A ⊓ B) = 0 := defect_of_le R le_rfl
  have hright : submodularDefect R B (A ⊓ B) = 0 := by
    rw [defect_symm]
    exact defect_of_le R inf_le_right
  have hleft : submodularDefect R A (A ⊓ B) = 0 := by
    rw [defect_symm]
    exact defect_of_le R inf_le_left
  rw [hself, hright, inf_eq_right.mpr (show A ⊓ B ≤ B from inf_le_right),
    hleft, hzero, mul_one, one_mul] at h
  exact h

/-- On disjoint assembly, the four meet ranks agree, and the defects do satisfy
the scalar associativity equation. This is a restriction on admissible inputs. -/
theorem disjoint_assembly_defect_assoc (R : SubmodularRank L) (A B C : L)
    (hmeets : R.rk (A ⊓ B) + R.rk ((A ⊔ B) ⊓ C) =
      R.rk (B ⊓ C) + R.rk (A ⊓ (B ⊔ C))) :
    submodularDefect R A B + submodularDefect R (A ⊔ B) C =
      submodularDefect R B C + submodularDefect R A (B ⊔ C) := by
  dsimp [submodularDefect]
  rw [sup_assoc]
  linarith

/-- The additive integer label has distinct normalized, compositional
interpretations, even before choosing a quantum amplitude space. -/
def labelInterpretation (scale : ℤ) (label : ℤ) : ℤ := scale * label

omit [Lattice L] in
theorem labelInterpretation_zero (scale : ℤ) : labelInterpretation scale 0 = 0 := by
  simp [labelInterpretation]

omit [Lattice L] in
theorem labelInterpretation_add (scale a b : ℤ) :
    labelInterpretation scale (a + b) =
      labelInterpretation scale a + labelInterpretation scale b := by
  dsimp [labelInterpretation]
  ring

omit [Lattice L] in
theorem labelInterpretation_distinct : labelInterpretation 1 1 ≠ labelInterpretation 2 1 := by
  norm_num [labelInterpretation]

omit [Lattice L] in
/-- Scalar classification after full neighbor symmetry has reduced a mixer to
`a I + b J`. Fixing the uniform vector and requiring a nonidentity involution
select the Grover reflection parameters. The symmetry reduction is described
in the accompanying report; this theorem verifies its algebraic conclusion. -/
theorem reflection_parameters (a b d : ℝ) (hd : d ≠ 0)
    (hfix : a + d * b = 1) (hinvolution : a ^ 2 = 1) (hnontrivial : a ≠ 1) :
    a = -1 ∧ b = 2 / d := by
  have hfactor : (a - 1) * (a + 1) = 0 := by nlinarith
  have ha : a = -1 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact False.elim (hnontrivial (by linarith))
    · linarith
  refine ⟨ha, (eq_div_iff hd).2 ?_⟩
  rw [ha] at hfix
  nlinarith

omit [Lattice L] in
/-- An additive-to-multiplicative integer-valued phase character is selected
as parity once a nonidentity involution on one unit of defect is required.
These are extra axioms, not consequences of submodularity. -/
theorem involutive_nontrivial_phase_unique (phase : ℕ → ℤ)
    (hzero : phase 0 = 1) (hadd : ∀ n m, phase (n + m) = phase n * phase m)
    (hinvolution : phase 1 * phase 1 = 1) (hnontrivial : phase 1 ≠ 1) :
    ∀ n, phase n = (-1 : ℤ) ^ n := by
  have hfactor : (phase 1 - 1) * (phase 1 + 1) = 0 := by nlinarith
  have hneg : phase 1 = -1 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact False.elim (hnontrivial (by linarith))
    · linarith
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih => rw [hadd, ih, hneg, pow_succ]

omit [Lattice L] in
/-- A square root of the nontrivial reflection eigenvalue leaves only the two
opposite quarter-turn choices. Selecting one is still an orientation choice. -/
theorem half_reflection_parameters (xi : ℂ) (hroot : xi ^ 2 = -1) :
    xi = Complex.I ∨ xi = -Complex.I := by
  have hfactor : (xi - Complex.I) * (xi + Complex.I) = 0 := by
    calc
      (xi - Complex.I) * (xi + Complex.I) = xi ^ 2 - Complex.I ^ 2 := by ring
      _ = 0 := by rw [hroot, Complex.I_sq]; ring
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

end TravelRuleSelection

#print axioms TravelRuleSelection.associative_join_phase_trivial
#print axioms TravelRuleSelection.associative_meet_phase_trivial
#print axioms TravelRuleSelection.disjoint_assembly_defect_assoc
#print axioms TravelRuleSelection.labelInterpretation_add
#print axioms TravelRuleSelection.labelInterpretation_distinct
#print axioms TravelRuleSelection.reflection_parameters
#print axioms TravelRuleSelection.involutive_nontrivial_phase_unique
#print axioms TravelRuleSelection.half_reflection_parameters
