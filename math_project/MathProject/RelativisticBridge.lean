import MathProject.DefectMassExploration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Normed

/-!
# Conditional structural-count bridge to relativistic matter

The mass-dependent mixing law is an added definition. We prove exact unitarity,
the actual real-parameter derivative of the walk at zero spacing, the Dirac
Hamiltonian/dispersion identities, and the positive-band curvature. A finite-time
continuum convergence theorem, curved propagation, and sourced Einstein dynamics
are not asserted here. See `new_frontiers/experiments/relativistic_bridge/README.md`.
-/

namespace RelativisticBridge

open Matrix Complex
open scoped Matrix.Norms.Elementwise

abbrev SpinMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- On-site direction mixing, with its angle supplied by the new law. -/
noncomputable def coin (θ : ℝ) : SpinMatrix :=
  !![(Real.cos θ : ℂ), -I * (Real.sin θ : ℂ);
     -I * (Real.sin θ : ℂ), (Real.cos θ : ℂ)]

/-- Momentum representation of the common conditional spatial shift. -/
noncomputable def shift (k : ℝ) : SpinMatrix :=
  !![(Real.cos k : ℂ) - I * (Real.sin k : ℂ), 0;
     0, (Real.cos k : ℂ) + I * (Real.sin k : ℂ)]

/-- Shared space/time spacing ε, fixed physical momentum p and mass m. -/
noncomputable def walk (ε p m : ℝ) : SpinMatrix := shift (ε * p) * coin (ε * m)

/-- H = p σ_z + m σ_x, in units c = ℏ = 1. -/
def diracHamiltonian (p m : ℝ) : SpinMatrix :=
  !![(p : ℂ), (m : ℂ); (m : ℂ), -(p : ℂ)]

private theorem complex_trig_norm (θ : ℝ) :
    (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq θ

/-- Exact finite-spacing unitarity; no continuum approximation. -/
theorem coin_unitary (θ : ℝ) : (coin θ).conjTranspose * coin θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coin, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring_nf <;> simp only [Complex.I_sq]
  all_goals linear_combination complex_trig_norm θ

theorem shift_unitary (k : ℝ) : (shift k).conjTranspose * shift k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shift, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring_nf <;> simp only [Complex.I_sq]
  all_goals linear_combination complex_trig_norm k

theorem walk_unitary (ε p m : ℝ) : (walk ε p m).conjTranspose * walk ε p m = 1 := by
  unfold walk
  rw [Matrix.conjTranspose_mul]
  calc
    (coin (ε * m)).conjTranspose * (shift (ε * p)).conjTranspose *
        (shift (ε * p) * coin (ε * m)) =
      (coin (ε * m)).conjTranspose *
        ((shift (ε * p)).conjTranspose * shift (ε * p)) * coin (ε * m) := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [shift_unitary, Matrix.mul_one, coin_unitary]

theorem walk_zero (p m : ℝ) : walk 0 p m = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [walk, shift, coin, Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact trace relation underlying cos ω = cos k cos θ. -/
theorem walk_trace (ε p m : ℝ) :
    Matrix.trace (walk ε p m) =
      2 * (Real.cos (ε * p) : ℂ) * (Real.cos (ε * m) : ℂ) := by
  simp [walk, shift, coin, Matrix.trace_fin_two]
  ring

/-- The full spinor Hamiltonian is Hermitian for real p and m. -/
theorem dirac_hermitian (p m : ℝ) :
    (diracHamiltonian p m).conjTranspose = diracHamiltonian p m := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diracHamiltonian, Matrix.conjTranspose_apply]

theorem dirac_square (p m : ℝ) :
    diracHamiltonian p m * diracHamiltonian p m =
      ((p ^ 2 + m ^ 2 : ℝ) : ℂ) • (1 : SpinMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The energy relation follows from the actual Hamiltonian characteristic polynomial. -/
theorem dirac_characteristic (E : ℂ) (p m : ℝ) :
    Matrix.det (E • (1 : SpinMatrix) - diracHamiltonian p m) =
      E ^ 2 - ((p ^ 2 + m ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.det_fin_two, diracHamiltonian]
  ring

private theorem cos_scaled_derivative (r : ℝ) :
    HasDerivAt (fun ε : ℝ => (Real.cos (ε * r) : ℂ)) 0 0 := by
  simpa using ((Real.hasDerivAt_cos (0 * r)).comp 0
    ((hasDerivAt_id (0 : ℝ)).mul_const r)).ofReal_comp

private theorem sin_scaled_derivative (r : ℝ) :
    HasDerivAt (fun ε : ℝ => (Real.sin (ε * r) : ℂ)) (r : ℂ) 0 := by
  simpa using ((Real.hasDerivAt_sin (0 * r)).comp 0
    ((hasDerivAt_id (0 : ℝ)).mul_const r)).ofReal_comp

/-- Actual first-order consistency theorem: dUε/dε at 0 is -iH.
This is not a theorem about iteration to finite continuum time. -/
theorem walk_generator (p m : ℝ) :
    HasDerivAt (fun ε : ℝ => walk ε p m)
      (-I • diracHamiltonian p m) 0 := by
  have hc := cos_scaled_derivative
  have hs := sin_scaled_derivative
  have hleft := (hc p).sub ((hs p).const_mul I)
  have hright := (hc p).add ((hs p).const_mul I)
  have hmix := (hs m).const_mul (-I)
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · convert! hleft.mul (hc m) using 1 <;>
      simp [walk, shift, coin, diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two,
        Pi.mul_def, Pi.sub_def]
  · convert! hleft.mul hmix using 1 <;>
      simp [walk, shift, coin, diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two,
        Pi.mul_def, Pi.sub_def]
  · convert! hright.mul hmix using 1 <;>
      simp [walk, shift, coin, diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two,
        Pi.mul_def, Pi.add_def]
  · convert! hright.mul (hc m) using 1 <;>
      simp [walk, shift, coin, diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two,
        Pi.mul_def, Pi.add_def]

/-- Positive continuum band; this is not the exact finite-lattice band. -/
noncomputable def energy (m p : ℝ) : ℝ := Real.sqrt (p ^ 2 + m ^ 2)

theorem energy_dispersion (m p : ℝ) : energy m p ^ 2 = p ^ 2 + m ^ 2 := by
  exact Real.sq_sqrt (by positivity)

theorem positive_energy_spectral (m p : ℝ) :
    Matrix.det ((energy m p : ℂ) • (1 : SpinMatrix) - diracHamiltonian p m) = 0 := by
  rw [dirac_characteristic]
  have h : (energy m p : ℂ) ^ 2 = ((p ^ 2 + m ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast energy_dispersion m p
  rw [h, sub_self]

theorem energy_at_rest (m : ℝ) (hm : 0 ≤ m) : energy m 0 = m := by
  simp [energy, Real.sqrt_sq hm]

theorem energy_derivative (m p : ℝ) (hm : 0 < m) :
    HasDerivAt (energy m) (p / energy m p) p := by
  have hpos : 0 < p ^ 2 + m ^ 2 := by positivity
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp p
    (((hasDerivAt_id p).pow 2).add_const (m ^ 2))
  convert! h using 1
  all_goals simp [energy]
  all_goals field_simp

/-- The second derivative at rest is 1/m; m>0 is essential. -/
theorem energy_curvature (m : ℝ) (hm : 0 < m) :
    HasDerivAt (deriv (energy m)) (1 / m) 0 := by
  have hderiv : deriv (energy m) = fun p => p / energy m p := by
    funext p
    exact (energy_derivative m p hm).deriv
  rw [hderiv]
  have h := (hasDerivAt_id (0 : ℝ)).div (energy_derivative m 0 hm)
    (by rw [energy_at_rest m hm.le]; exact ne_of_gt hm)
  convert! h using 1
  all_goals simp [energy_at_rest m hm.le]
  all_goals field_simp [ne_of_gt hm]

/-- Explicit ADDED law: one common scale couples intrinsic count to Dirac mass. -/
def countMass (g : ℝ) (M : ℕ) : ℝ := g * M

theorem count_rest_energy (g : ℝ) (M : ℕ) (hg : 0 < g) :
    energy (countMass g M) 0 = countMass g M := by
  apply energy_at_rest
  unfold countMass
  positivity

theorem count_inertia (g : ℝ) (M : ℕ) (hg : 0 < g) (hM : 0 < M) :
    (deriv (deriv (energy (countMass g M))) 0)⁻¹ = countMass g M := by
  have hm : 0 < countMass g M := by unfold countMass; positivity
  rw [(energy_curvature (countMass g M) hm).deriv]
  simp

/-- Zero count removes the directional mixing exactly, even at finite spacing. -/
theorem zero_count_walk (ε p g : ℝ) : walk ε p (countMass g 0) = shift (ε * p) := by
  have hzero : coin 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coin]
  simp [walk, countMass, hzero]

/-- Structural mass from the original lattice enters only through the added coupling. -/
def latticeMass {L : Type*} [Lattice L] (g : ℝ)
    (N : FunctorialGeometry.ModularRank L) (R : FunctorialGeometry.SubmodularRank L)
    (A : L) : ℝ := g * (DefectMassExploration.structuralMass N R A : ℝ)

/-- The original defect/excess identity survives the explicitly chosen coupling. -/
theorem lattice_defect_excess {L : Type*} [Lattice L] (g : ℝ)
    (N : FunctorialGeometry.ModularRank L) (R : FunctorialGeometry.SubmodularRank L)
    (A B : L) :
    g * (FunctorialGeometry.submodularDefect R A B : ℝ) =
      latticeMass g N R (A ⊔ B) + latticeMass g N R (A ⊓ B) -
        latticeMass g N R A - latticeMass g N R B := by
  rw [DefectMassExploration.defect_eq_mass_excess N R]
  unfold latticeMass
  push_cast
  ring

/-- Positive intrinsic structural mass has the Dirac curvature mass, conditionally
on the added coupling. No positivity assumption is inferred from submodularity. -/
theorem lattice_inertia {L : Type*} [Lattice L] (g : ℝ)
    (N : FunctorialGeometry.ModularRank L) (R : FunctorialGeometry.SubmodularRank L)
    (A : L) (hg : 0 < g) (hA : 0 < DefectMassExploration.structuralMass N R A) :
    (deriv (deriv (energy (latticeMass g N R A))) 0)⁻¹ = latticeMass g N R A := by
  have hm : 0 < latticeMass g N R A := by
    unfold latticeMass
    exact mul_pos hg (by exact_mod_cast hA)
  rw [(energy_curvature (latticeMass g N R A) hm).deriv]
  simp

/-- The rational coin's diagonal coefficient. -/
noncomputable def rationalC (b : ℝ) : ℝ := (1 - b ^ 2) / (1 + b ^ 2)

/-- The rational coin's direction-mixing coefficient. -/
noncomputable def rationalS (b : ℝ) : ℝ := 2 * b / (1 + b ^ 2)

noncomputable def rationalCoin (b : ℝ) : SpinMatrix :=
  !![(rationalC b : ℂ), -I * (rationalS b : ℂ);
     -I * (rationalS b : ℂ), (rationalC b : ℂ)]

noncomputable def rationalWalk (ε p m : ℝ) : SpinMatrix :=
  shift (ε * p) * rationalCoin (ε * m / 2)

theorem rational_circle (b : ℝ) : rationalC b ^ 2 + rationalS b ^ 2 = 1 := by
  have hd : 1 + b ^ 2 ≠ 0 := by positivity
  unfold rationalC rationalS
  field_simp
  ring

theorem rational_coin_unitary (b : ℝ) :
    (rationalCoin b).conjTranspose * rationalCoin b = 1 := by
  have h : (rationalC b : ℂ) ^ 2 + (rationalS b : ℂ) ^ 2 = 1 := by
    exact_mod_cast rational_circle b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalCoin, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
      ring_nf <;> simp only [Complex.I_sq]
  all_goals linear_combination h

theorem rational_walk_unitary (ε p m : ℝ) :
    (rationalWalk ε p m).conjTranspose * rationalWalk ε p m = 1 := by
  unfold rationalWalk
  rw [Matrix.conjTranspose_mul]
  calc
    (rationalCoin (ε * m / 2)).conjTranspose * (shift (ε * p)).conjTranspose *
        (shift (ε * p) * rationalCoin (ε * m / 2)) =
      (rationalCoin (ε * m / 2)).conjTranspose *
        ((shift (ε * p)).conjTranspose * shift (ε * p)) * rationalCoin (ε * m / 2) := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [shift_unitary, Matrix.mul_one, rational_coin_unitary]

private theorem rational_scaled_derivatives (m : ℝ) :
    HasDerivAt (fun ε : ℝ => (rationalC (ε * m / 2) : ℂ)) 0 0 ∧
    HasDerivAt (fun ε : ℝ => (rationalS (ε * m / 2) : ℂ)) (m : ℂ) 0 := by
  have ha := ((hasDerivAt_id (0 : ℝ)).mul_const m).div_const 2
  have hsq := ha.pow 2
  have hc := (hsq.const_sub 1).div (hsq.const_add 1) (by norm_num)
  have hs := (ha.const_mul 2).div (hsq.const_add 1) (by norm_num)
  constructor
  · simpa [rationalC, Pi.sub_def, Pi.add_def, Pi.div_def] using hc.ofReal_comp
  · convert! hs.ofReal_comp using 1
    all_goals norm_num
    all_goals ring

/-- The exactly rational finite-step coin has the same actual Dirac generator. -/
theorem rational_walk_generator (p m : ℝ) :
    HasDerivAt (fun ε : ℝ => rationalWalk ε p m)
      (-I • diracHamiltonian p m) 0 := by
  have hleft := (cos_scaled_derivative p).sub ((sin_scaled_derivative p).const_mul I)
  have hright := (cos_scaled_derivative p).add ((sin_scaled_derivative p).const_mul I)
  obtain ⟨hc, hs⟩ := rational_scaled_derivatives m
  have hmix := hs.const_mul (-I)
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · convert! hleft.mul hc using 1 <;>
      simp [rationalWalk, shift, rationalCoin, rationalC, rationalS,
        diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two, Pi.mul_def, Pi.sub_def]
  · convert! hleft.mul hmix using 1 <;>
      simp [rationalWalk, shift, rationalCoin, rationalC, rationalS,
        diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two, Pi.mul_def, Pi.sub_def]
  · convert! hright.mul hmix using 1 <;>
      simp [rationalWalk, shift, rationalCoin, rationalC, rationalS,
        diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two, Pi.mul_def, Pi.add_def]
  · convert! hright.mul hc using 1 <;>
      simp [rationalWalk, shift, rationalCoin, rationalC, rationalS,
        diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two, Pi.mul_def, Pi.add_def]

end RelativisticBridge

#print axioms RelativisticBridge.coin_unitary
#print axioms RelativisticBridge.walk_unitary
#print axioms RelativisticBridge.walk_generator
#print axioms RelativisticBridge.dirac_square
#print axioms RelativisticBridge.positive_energy_spectral
#print axioms RelativisticBridge.energy_curvature
#print axioms RelativisticBridge.count_inertia
#print axioms RelativisticBridge.zero_count_walk
#print axioms RelativisticBridge.lattice_defect_excess
#print axioms RelativisticBridge.lattice_inertia
#print axioms RelativisticBridge.rational_walk_unitary
#print axioms RelativisticBridge.rational_walk_generator
