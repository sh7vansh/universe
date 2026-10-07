import MathProject.DefectMassExploration
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Consequences of explicitly added candidate-universe laws

These results do not identify structural defect with physical mass or derive
gravity. They isolate the phase-only obstruction and verify a separate real
Cartan source-field extension. The latter requires an additional source axiom.
-/

namespace ProposedUniverse

section PhaseTravel

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Iteration of a fixed linear travel rule with a uniform scalar phase. -/
def phasedTravel (T : V →ₗ[ℂ] V) (z : ℂ) : ℕ → V → V
  | 0, v => v
  | n + 1, v => z • T (phasedTravel T z n v)

/-- A spatially uniform phase cannot change the route amplitudes except by an
overall scalar. This applies to every number of steps, not only finite tests. -/
theorem phasedTravel_eq (T : V →ₗ[ℂ] V) (z : ℂ) (n : ℕ) (v : V) :
    phasedTravel T z n v = z ^ n • phasedTravel T 1 n v := by
  induction n with
  | zero => simp [phasedTravel]
  | succ n ih =>
    simp only [phasedTravel, ih, map_smul, one_smul, smul_smul]
    rw [pow_succ]
    congr 1
    ring

/-- The chosen parity response cannot distinguish counts differing by two. -/
theorem parity_phase_alias (m : ℕ) :
    (-1 : ℂ) ^ (m + 2) = (-1 : ℂ) ^ m := by
  rw [pow_add]
  norm_num

end PhaseTravel

/-- Coordinate probabilities agree when the uniform phase has norm one.
The linear rule need not even be unitary for this particular statement. -/
theorem uniform_phase_probability {I : Type*} (T : (I → ℂ) →ₗ[ℂ] (I → ℂ))
    (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) (v : I → ℂ) (i : I) :
    ‖phasedTravel T z n v i‖ ^ 2 = ‖phasedTravel T 1 n v i‖ ^ 2 := by
  rw [phasedTravel_eq]
  simp [Pi.smul_apply, smul_eq_mul, norm_pow, hz]

section SourceField

/-- Real extension of the existing A₃ Dirichlet-Cartan quadratic form. -/
def fieldQuadratic (a b c : ℝ) : ℝ :=
  a ^ 2 + (a - b) ^ 2 + (b - c) ^ 2 + c ^ 2

/-- An ADDITIONAL source action; the source term is not in the original rank axioms. -/
noncomputable def sourceEnergy (ra rb rc a b c : ℝ) : ℝ :=
  fieldQuadratic a b c / 2 - (ra * a + rb * b + rc * c)

theorem fieldQuadratic_nonneg (a b c : ℝ) : 0 ≤ fieldQuadratic a b c := by
  unfold fieldQuadratic
  positivity

/-- The discrete source equation is equivalent to vanishing linear terms in
the energy increment. The remaining increment is positive quadratic energy. -/
theorem source_energy_completion (ra rb rc a b c da db dc : ℝ)
    (ha : 2 * a - b = ra) (hb : 2 * b - a - c = rb) (hc : 2 * c - b = rc) :
    sourceEnergy ra rb rc (a + da) (b + db) (c + dc) =
      sourceEnergy ra rb rc a b c + fieldQuadratic da db dc / 2 := by
  rw [← ha, ← hb, ← hc]
  dsimp [sourceEnergy, fieldQuadratic]
  ring

theorem source_equation_minimizes_energy (ra rb rc a b c da db dc : ℝ)
    (ha : 2 * a - b = ra) (hb : 2 * b - a - c = rb) (hc : 2 * c - b = rc) :
    sourceEnergy ra rb rc a b c ≤
      sourceEnergy ra rb rc (a + da) (b + db) (c + dc) := by
  rw [source_energy_completion ra rb rc a b c da db dc ha hb hc]
  have h := fieldQuadratic_nonneg da db dc
  linarith

/-- Exact inverse of A₃ acting on the source. -/
theorem source_field_three (ra rb rc : ℝ) :
    let a := (3 * ra + 2 * rb + rc) / 4
    let b := (ra + 2 * rb + rc) / 2
    let c := (ra + 2 * rb + 3 * rc) / 4
    2 * a - b = ra ∧ 2 * b - a - c = rb ∧ 2 * c - b = rc := by
  dsimp
  constructor
  · ring
  constructor <;> ring

/-- A cross-potential -q_source*q_probe*Green(x,y) is lower wherever the
Green function is larger. This is only a static attraction criterion. -/
theorem cross_potential_attraction (source probe near far : ℝ)
    (hs : 0 < source) (hp : 0 < probe) (hg : far < near) :
    -(source * probe) * near < -(source * probe) * far := by
  have hprod : 0 < source * probe := mul_pos hs hp
  nlinarith

end SourceField

end ProposedUniverse

#print axioms ProposedUniverse.phasedTravel_eq
#print axioms ProposedUniverse.uniform_phase_probability
#print axioms ProposedUniverse.parity_phase_alias
#print axioms ProposedUniverse.source_energy_completion
#print axioms ProposedUniverse.source_equation_minimizes_energy
#print axioms ProposedUniverse.source_field_three
#print axioms ProposedUniverse.cross_potential_attraction
