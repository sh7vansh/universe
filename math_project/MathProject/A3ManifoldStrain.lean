import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Cover
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace A3ManifoldStrain

/-!
# A3 Root Lattice Metric, Cartan Form, and Manifold Strain Friction

This module formalizes:
1. The A3 Cartan Matrix as a positive-definite Riemannian metric on Z^3.
2. The Killing-Cartan bilinear form and the sum-of-squares decomposition.
3. The 6 positive roots and their invariant squared norm (= 2).
4. The off-diagonal strain coupling (adjacent roots have strain -1, non-adjacent 0).
5. Manifold strain energy as the continuous/geometric analogue of algorithmic friction.
-/

/-- Vector in the 3D root space Z^3. -/
@[ext]
structure Vec3 where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq, Repr

namespace Vec3

def zero : Vec3 := ⟨0, 0, 0⟩
def add (u v : Vec3) : Vec3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def sub (u v : Vec3) : Vec3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

instance : Zero Vec3 := ⟨zero⟩
instance : Add Vec3 := ⟨add⟩
instance : Sub Vec3 := ⟨sub⟩

@[simp] theorem zero_x : (0 : Vec3).x = 0 := rfl
@[simp] theorem zero_y : (0 : Vec3).y = 0 := rfl
@[simp] theorem zero_z : (0 : Vec3).z = 0 := rfl

@[simp] theorem add_x (u v : Vec3) : (u + v).x = u.x + v.x := rfl
@[simp] theorem add_y (u v : Vec3) : (u + v).y = u.y + v.y := rfl
@[simp] theorem add_z (u v : Vec3) : (u + v).z = u.z + v.z := rfl

end Vec3

open Vec3

/-- The A3 Cartan Bilinear Form (the Riemannian metric tensor on the root space).
    Matrix A = [[2, -1, 0], [-1, 2, -1], [0, -1, 2]]
    <u, v> = 2*u.x*v.x + 2*u.y*v.y + 2*u.z*v.z - (u.x*v.y + u.y*v.x) - (u.y*v.z + u.z*v.y) -/
def cartanForm (u v : Vec3) : ℤ :=
  2 * u.x * v.x + 2 * u.y * v.y + 2 * u.z * v.z -
  (u.x * v.y + u.y * v.x) - (u.y * v.z + u.z * v.y)

/-- The Cartan form is symmetric: <u, v> = <v, u>. -/
theorem cartanForm_symm (u v : Vec3) : cartanForm u v = cartanForm v u := by
  dsimp [cartanForm]
  ring

/-- Sum-of-squares decomposition of the A3 metric:
    <v, v> = v.x^2 + (v.x - v.y)^2 + (v.y - v.z)^2 + v.z^2 -/
theorem cartanForm_sum_of_squares (v : Vec3) :
    cartanForm v v = v.x^2 + (v.x - v.y)^2 + (v.y - v.z)^2 + v.z^2 := by
  dsimp [cartanForm]
  ring

/-- Positive semi-definiteness: <v, v> ≥ 0 for all v. -/
theorem cartanForm_nonneg (v : Vec3) : 0 ≤ cartanForm v v := by
  rw [cartanForm_sum_of_squares]
  have h1 : 0 ≤ v.x^2 := sq_nonneg v.x
  have h2 : 0 ≤ (v.x - v.y)^2 := sq_nonneg (v.x - v.y)
  have h3 : 0 ≤ (v.y - v.z)^2 := sq_nonneg (v.y - v.z)
  have h4 : 0 ≤ v.z^2 := sq_nonneg v.z
  linarith

/-- Positive definiteness: <v, v> = 0 iff v = 0. -/
theorem cartanForm_pos_def (v : Vec3) : cartanForm v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [cartanForm_sum_of_squares] at h
    have hx2 : 0 ≤ v.x^2 := sq_nonneg v.x
    have hxy2 : 0 ≤ (v.x - v.y)^2 := sq_nonneg (v.x - v.y)
    have hyz2 : 0 ≤ (v.y - v.z)^2 := sq_nonneg (v.y - v.z)
    have hz2 : 0 ≤ v.z^2 := sq_nonneg v.z
    have hx0 : v.x = 0 := by nlinarith
    have hz0 : v.z = 0 := by nlinarith
    have hy0 : v.y = 0 := by nlinarith
    ext
    · exact hx0
    · exact hy0
    · exact hz0
  · rintro rfl
    rfl

/-!
### The 6 Positive Roots of A3 and their Invariant Metric Norms
-/

def alpha1 : Vec3 := ⟨1, 0, 0⟩
def alpha2 : Vec3 := ⟨0, 1, 0⟩
def alpha3 : Vec3 := ⟨0, 0, 1⟩
def alpha12 : Vec3 := ⟨1, 1, 0⟩
def alpha23 : Vec3 := ⟨0, 1, 1⟩
def alpha123 : Vec3 := ⟨1, 1, 1⟩

/-- Every positive root of A3 has identical squared norm = 2. -/
theorem norm_alpha1 : cartanForm alpha1 alpha1 = 2 := by rfl
theorem norm_alpha2 : cartanForm alpha2 alpha2 = 2 := by rfl
theorem norm_alpha3 : cartanForm alpha3 alpha3 = 2 := by rfl
theorem norm_alpha12 : cartanForm alpha12 alpha12 = 2 := by rfl
theorem norm_alpha23 : cartanForm alpha23 alpha23 = 2 := by rfl
theorem norm_alpha123 : cartanForm alpha123 alpha123 = 2 := by rfl

/-!
### The Off-Diagonal Strain Couplings
-/

/-- Adjacent roots α₁ and α₂ experience mutual shear strain = -1 (angle = 120 deg). -/
theorem strain_adjacent_12 : cartanForm alpha1 alpha2 = -1 := by rfl

/-- Adjacent roots α₂ and α₃ experience mutual shear strain = -1 (angle = 120 deg). -/
theorem strain_adjacent_23 : cartanForm alpha2 alpha3 = -1 := by rfl

/-- Non-adjacent roots α₁ and α₃ are uncoupled (orthogonal, strain = 0). -/
theorem strain_orthogonal_13 : cartanForm alpha1 alpha3 = 0 := by rfl

/-!
### Manifold Strain Energy as Algorithmic Friction
-/

/-- The Manifold Strain Energy of a state transition v in the A3 root space. -/
def strainEnergy (v : Vec3) : ℤ :=
  cartanForm v v

/-- Manifold strain is strictly non-negative (friction lower bound). -/
theorem strain_nonneg (v : Vec3) : 0 ≤ strainEnergy v :=
  cartanForm_nonneg v

/-- Zero strain energy implies zero displacement (resting equilibrium). -/
theorem strain_zero_iff (v : Vec3) : strainEnergy v = 0 ↔ v = 0 :=
  cartanForm_pos_def v

/-- The composite strain when activating two coupled roots α₁ and α₂:
    Strain(α₁ + α₂) = Strain(α₁) + Strain(α₂) + 2*Coupling(α₁, α₂) = 2 + 2 - 2 = 2. -/
theorem coupled_strain_alpha12 :
    strainEnergy alpha12 = strainEnergy alpha1 + strainEnergy alpha2 + 2 * cartanForm alpha1 alpha2 := by
  rfl

end A3ManifoldStrain
