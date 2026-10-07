import MathProject.RelativisticBridge

/-!
# Which composition laws select count-proportional mixing?

All composition and symmetry laws below are explicit hypotheses. They are not
new axioms and do not follow from submodular rank. Count composition determines
powers of one gate. Its actual derivative at zero determines an additive
generator. Hermitian, direction-exchange symmetric, traceless generators have
Dirac mixing form. This identifies a sufficient extra principle, not a graph
derivation of that principle or a finite-time convergence proof.
-/

namespace StructuralMixing

open Matrix Complex RelativisticBridge
open scoped Matrix.Norms.Elementwise

/-- Multiplicative count composition determines every response from one unit. -/
theorem response_powers {G : Type*} [Monoid G] (C : ℕ → G)
    (hzero : C 0 = 1) (hadd : ∀ n r, C (n + r) = C n * C r) (n : ℕ) :
    C n = C 1 ^ n := by
  induction n with
  | zero => simpa using hzero
  | succ n ih => rw [hadd n 1, ih, pow_succ]

/-- An additive count generator is linear. The elementary rate remains free. -/
theorem additive_rate_linear (a : ℕ → ℝ) (hzero : a 0 = 0)
    (hadd : ∀ n r, a (n + r) = a n + a r) (n : ℕ) :
    a n = (n : ℝ) * a 1 := by
  induction n with
  | zero => simpa using hzero
  | succ n ih => rw [hadd n 1, ih]; push_cast; ring

theorem additive_generator_linear (A : ℕ → SpinMatrix) (hzero : A 0 = 0)
    (hadd : ∀ n r, A (n + r) = A n + A r) (n : ℕ) :
    A n = n • A 1 := by
  induction n with
  | zero => simpa using hzero
  | succ n ih => rw [hadd n 1, ih, add_nsmul, one_nsmul]

/-- Scalar coefficient after repeating a matrix generator n times. -/
theorem repeat_dirac_mixing (g : ℝ) (n : ℕ) :
    n • diracHamiltonian 0 g = diracHamiltonian 0 ((n : ℝ) * g) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diracHamiltonian, nsmul_eq_mul]

/-- The physical direction-exchange operator. -/
def directionSwap : SpinMatrix := diracHamiltonian 0 1

/-- With scalar energy shifts removed, exchange symmetry leaves a real
multiple of σ_x. Symmetry does not fix that multiple or require it nonzero. -/
theorem symmetric_generator_form (A : SpinMatrix)
    (hhermitian : A.conjTranspose = A)
    (hexchange : A * directionSwap = directionSwap * A)
    (htrace : Matrix.trace A = 0) :
    ∃ g : ℝ, A = diracHamiltonian 0 g := by
  have hoff : A 0 1 = A 1 0 := by
    have h := congrArg (fun B : SpinMatrix => B 0 0) hexchange
    simpa [directionSwap, diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two] using h
  have hdiag : A 0 0 = A 1 1 := by
    have h := congrArg (fun B : SpinMatrix => B 0 1) hexchange
    simpa [directionSwap, diracHamiltonian, Matrix.mul_apply, Fin.sum_univ_two] using h
  have hsum : A 0 0 + A 1 1 = 0 := by simpa [Matrix.trace_fin_two] using htrace
  have h00 : A 0 0 = 0 := by linear_combination (hsum + hdiag) / 2
  have h11 : A 1 1 = 0 := hdiag.symm.trans h00
  have hreal : (starRingEnd ℂ) (A 0 1) = A 0 1 := by
    have h := congrArg (fun B : SpinMatrix => B 0 1) hhermitian
    simpa [Matrix.conjTranspose_apply, ← hoff, Complex.star_def] using h
  obtain ⟨g, hg⟩ := Complex.conj_eq_iff_real.mp hreal
  refine ⟨g, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diracHamiltonian, h00, h11, hg, ← hoff]

/-- Entrywise product rule in the same norm used by RelativisticBridge. -/
private theorem matrix_product_derivative (F G : ℝ → SpinMatrix)
    (A B : SpinMatrix) (hF : HasDerivAt F A 0) (hG : HasDerivAt G B 0) :
    HasDerivAt (fun ε => F ε * G ε) (A * G 0 + F 0 * B) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hf := fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hF i) j
  have hg := fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hG i) j
  have h := ((hf i 0).mul (hg 0 j)).add ((hf i 1).mul (hg 1 j))
  convert! h using 1
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.add_def, Pi.mul_def]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- Actual derivative of n repeated elementary gates at the identity. -/
theorem repeated_gate_derivative (F : ℝ → SpinMatrix) (A : SpinMatrix)
    (hFzero : F 0 = 1) (hF : HasDerivAt F A 0) (n : ℕ) :
    HasDerivAt (fun ε => F ε ^ n) (n • A) 0 := by
  induction n with
  | zero =>
    convert! hasDerivAt_const (0 : ℝ) (1 : SpinMatrix) using 1
    all_goals simp
  | succ n ih =>
    have h := matrix_product_derivative (fun ε => F ε ^ n) F (n • A) A ih hF
    change HasDerivAt (fun ε => F ε ^ (n + 1)) ((n + 1) • A) 0
    rw [add_nsmul, one_nsmul]
    convert! h using 1
    all_goals simp [hFzero]

/-- The count-composition hypothesis derives the generator for every count. -/
theorem compositional_response_derivative (C : ℕ → ℝ → SpinMatrix)
    (hcountzero : ∀ ε, C 0 ε = 1)
    (hcompose : ∀ n r ε, C (n + r) ε = C n ε * C r ε)
    (hunitzero : C 1 0 = 1) (A : SpinMatrix)
    (hunit : HasDerivAt (C 1) A 0) (n : ℕ) :
    HasDerivAt (C n) (n • A) 0 := by
  have heq : C n = fun ε => C 1 ε ^ n := by
    funext ε
    exact response_powers (fun k => C k ε) (hcountzero ε)
      (fun k r => hcompose k r ε) n
  rw [heq]
  exact repeated_gate_derivative (C 1) A hunitzero hunit n

/-- Count composition and a one-unit Dirac mixing rate select m = n*g
at first order, instead of defining a separate rate for each n. -/
theorem compositional_dirac_generator (C : ℕ → ℝ → SpinMatrix)
    (hcountzero : ∀ ε, C 0 ε = 1)
    (hcompose : ∀ n r ε, C (n + r) ε = C n ε * C r ε)
    (hunitzero : C 1 0 = 1) (g : ℝ)
    (hunit : HasDerivAt (C 1) (-I • diracHamiltonian 0 g) 0) (n : ℕ) :
    HasDerivAt (C n) (-I • diracHamiltonian 0 ((n : ℝ) * g)) 0 := by
  have h := compositional_response_derivative C hcountzero hcompose hunitzero
    (-I • diracHamiltonian 0 g) hunit n
  have heq : n • (-I • diracHamiltonian 0 g) =
      -I • diracHamiltonian 0 ((n : ℝ) * g) := by
    rw [← repeat_dirac_mixing]
    exact smul_comm n (-I) (diracHamiltonian 0 g)
  rw [heq] at h
  exact h

/-- Composition plus Hermitian exchange symmetry selects the Dirac form and
linear count dependence together. The common real coefficient remains free. -/
theorem compositional_symmetric_dirac (C : ℕ → ℝ → SpinMatrix)
    (hcountzero : ∀ ε, C 0 ε = 1)
    (hcompose : ∀ n r ε, C (n + r) ε = C n ε * C r ε)
    (hunitzero : C 1 0 = 1) (A : SpinMatrix)
    (hunit : HasDerivAt (C 1) (-I • A) 0)
    (hhermitian : A.conjTranspose = A)
    (hexchange : A * directionSwap = directionSwap * A)
    (htrace : Matrix.trace A = 0) :
    ∃ g : ℝ, ∀ n : ℕ,
      HasDerivAt (C n) (-I • diracHamiltonian 0 ((n : ℝ) * g)) 0 := by
  obtain ⟨g, hg⟩ := symmetric_generator_form A hhermitian hexchange htrace
  rw [hg] at hunit
  exact ⟨g, compositional_dirac_generator C hcountzero hcompose hunitzero g hunit⟩

/-- A concrete compositional response: repeat one rational gate on a common
direction state. No count-dependent mass is supplied to the elementary gate. -/
noncomputable def rationalCountResponse (n : ℕ) (ε : ℝ) : SpinMatrix :=
  rationalCoin (ε / 2) ^ n

theorem rational_count_composes (n r : ℕ) (ε : ℝ) :
    rationalCountResponse (n + r) ε =
      rationalCountResponse n ε * rationalCountResponse r ε := by
  exact pow_add _ n r

/-- The explicit repeated elementary gate derives m=n at first order. -/
theorem rational_count_generator (n : ℕ) :
    HasDerivAt (rationalCountResponse n)
      (-I • diracHamiltonian 0 (n : ℝ)) 0 := by
  have hshift : shift 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [shift]
  have hcoin : rationalCoin 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rationalCoin, rationalC, rationalS]
  have hunit : HasDerivAt (rationalCountResponse 1)
      (-I • diracHamiltonian 0 1) 0 := by
    have heq : rationalCountResponse 1 = fun ε => rationalCoin (ε / 2) := by
      funext ε
      simp [rationalCountResponse]
    rw [heq]
    convert! rational_walk_generator 0 1 using 1
    all_goals simp [rationalWalk, hshift]
  have h := compositional_dirac_generator rationalCountResponse
    (by intro ε; simp [rationalCountResponse]) rational_count_composes
    (by simp [rationalCountResponse, hcoin]) 1 hunit n
  simpa using h

/-- Translation uses one common tick; only the elementary mixing repeats. -/
noncomputable def compositionalWalk (n : ℕ) (p ε : ℝ) : SpinMatrix :=
  shift (ε * p) * rationalCountResponse n ε

private theorem unitary_product (A B : SpinMatrix)
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (A * B).conjTranspose * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc
    B.conjTranspose * A.conjTranspose * (A * B) =
        B.conjTranspose * (A.conjTranspose * A) * B := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hB]

theorem rational_count_unitary (n : ℕ) (ε : ℝ) :
    (rationalCountResponse n ε).conjTranspose * rationalCountResponse n ε = 1 := by
  unfold rationalCountResponse
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact unitary_product _ _ ih (rational_coin_unitary _)

theorem compositional_walk_unitary (n : ℕ) (p ε : ℝ) :
    (compositionalWalk n p ε).conjTranspose * compositionalWalk n p ε = 1 := by
  exact unitary_product _ _ (shift_unitary _) (rational_count_unitary n ε)

/-- The repeated-gate model reaches the same actual Dirac generator, with
count dependence derived from repetition and one common transport speed. -/
theorem compositional_walk_generator (n : ℕ) (p : ℝ) :
    HasDerivAt (compositionalWalk n p)
      (-I • diracHamiltonian p (n : ℝ)) 0 := by
  have hcoin : rationalCoin 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rationalCoin, rationalC, rationalS]
  have hshiftzero : shift 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [shift]
  have hshift : HasDerivAt (fun ε => shift (ε * p))
      (-I • diracHamiltonian p 0) 0 := by
    convert! rational_walk_generator p 0 using 1
    all_goals simp [rationalWalk, hcoin]
  have h := matrix_product_derivative _ _ _ _ hshift (rational_count_generator n)
  have hzero : rationalCountResponse n 0 = 1 := by
    simp [rationalCountResponse, hcoin]
  simp only [hzero, zero_mul, hshiftzero, Matrix.mul_one, Matrix.one_mul] at h
  convert! h using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diracHamiltonian]

/-- Canonical cycle-space trace is a count, but normalized reduction removes
that factor. This algebraic statement does not postulate a coupling. -/
theorem identity_trace (n : ℕ) : Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) = n := by
  simp [Matrix.trace]

theorem normalized_identity_trace (n : ℕ) (hn : 0 < n) :
    Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) / n = 1 := by
  rw [identity_trace]
  exact div_self (by exact_mod_cast ne_of_gt hn)

end StructuralMixing

#print axioms StructuralMixing.response_powers
#print axioms StructuralMixing.symmetric_generator_form
#print axioms StructuralMixing.repeated_gate_derivative
#print axioms StructuralMixing.compositional_response_derivative
#print axioms StructuralMixing.compositional_dirac_generator
#print axioms StructuralMixing.compositional_symmetric_dirac
#print axioms StructuralMixing.rational_count_generator
#print axioms StructuralMixing.compositional_walk_unitary
#print axioms StructuralMixing.compositional_walk_generator
#print axioms StructuralMixing.identity_trace
