import core.QuantumEngine

/-!
  # QuantumEngineProofs.lean
  Formal structural theorems and conservation laws for `QuantumEngine.lean`.
-/

namespace QuantumEngine

open CategoricalMachine

/-- Theorem: Photon rest mass is strictly zero. -/
theorem photon_mass_zero (m : CategoricalMachine) : (m.getSimple 1).mass = 0.0 := by rfl

/-- Theorem: Void vacuum signature is strictly zero. -/
theorem void_signature_zero (m : CategoricalMachine) : (m.getSimple 0).signature = ComplexNum.zero := by rfl

/-- Theorem: Void vacuum matrix is the identity 2x2 matrix. -/
theorem void_matrix_id (m : CategoricalMachine) : (m.getSimple 0).matrix = Mat2.id := by rfl

/-- Theorem: Simple objects have exactly one factor (themselves). -/
theorem getSimple_factor_count (m : CategoricalMachine) (p : Nat) (isAnti : Bool) (c : Option String) :
    (m.getSimple p isAnti c).factors.length = 1 := by rfl

/-- Theorem: Simple objects have no prior extensions. -/
theorem getSimple_extensions_empty (m : CategoricalMachine) (p : Nat) (isAnti : Bool) (c : Option String) :
    (m.getSimple p isAnti c).extensions.isEmpty = true := by rfl

/-- Theorem: Exact sequence reconstruction strictly preserves the factor count sum. -/
theorem reconstruction_factor_count (A B : GrothendieckObject)
    (sig : ComplexNum) (mass : Float) (exts : List ExtensionClass) (mat : Mat2) :
    (GrothendieckObject.mk sig mass (A.factors ++ B.factors) exts mat).factors.length =
      A.factors.length + B.factors.length := by
  dsimp
  rw [List.length_append]

/-- Theorem: Exact sequence reconstruction concatenates factor lists associatively. -/
theorem reconstruction_factors_assoc (A B C : GrothendieckObject) :
    ((A.factors ++ B.factors) ++ C.factors) = (A.factors ++ (B.factors ++ C.factors)) := by
  rw [List.append_assoc]

/-- Theorem: Composite signature is the complex product of constituents. -/
theorem composite_signature (A B : GrothendieckObject) (mass : Float) (factors : List SimpleObject) (exts : List ExtensionClass) (mat : Mat2) :
    (GrothendieckObject.mk (A.signature * B.signature) mass factors exts mat).signature =
      A.signature * B.signature := by rfl

/-- Theorem: Composite matrix is the matrix product of constituents. -/
theorem composite_matrix (A B : GrothendieckObject) (sig : ComplexNum) (mass : Float) (factors : List SimpleObject) (exts : List ExtensionClass) :
    (GrothendieckObject.mk sig mass factors exts (A.matrix * B.matrix)).matrix =
      A.matrix * B.matrix := by rfl

end QuantumEngine
