/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Order.Closure
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fintype.Basic
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import MathProject.AssociahedralFacetProducts

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Functorial and Geometric Structures on Subobject Lattices

This unified module formalizes the mathematical core corresponding to `thin-category-lattice.md`:
The overview follows the paper order. The declarations retain their existing order.
Part and section labels below refer to the paper.

1. **Thin Categories & Subobject Lattices:** Posets as thin categories, subsingleton homs,
   monic/epic collapse, meets/joins as universal products/coproducts, closure monads.
2. **Submodular Defects & Modularity:** Defect Δ(A, B) ≥ 0, modularity characterization,
   and the meet interaction.
3. **Higher Associativity & Root Labels:** Tamari lattice 𝒯₄ (Catalan C₃ = 5),
   all-arity bracket/face order isomorphisms and thin-category evaluation (imported
   from `AssociahedralComposition`), the general tree-to-vertex equivalence,
   Loday's convex realization with its full supporting-face order, affine dimension,
   geometric Catalan vertex count and geometric facet count in every dimension,
   facet product face orders, root indexing of actual supporting facets, and
   the pentagonal and square facet types and counts for K₅.
4. **Cartan Metric & Quadratic Form:** Positive-definite quadratic form on ℤ³,
   sum-of-squares decomposition, root norm invariance (= 2), and off-diagonal shear couplings.
5. **The Travel Experience Monoid:** 2×2 unipotent shear group, travel state (action, transport),
   monoid associativity/unitality, path valuation, strict action growth, coordinate sums,
   and equal arrow and valuation evaluations for all full bracket patterns of a fixed chain.
6. **Transfinite Cellular Filtrations & Basis Discovery:** Transfinite Cellular sequence on
   semi-Artinian objects, stabilization at Cellular length Ω, reconstruction, SES presentation,
   vanishing residual colimits on restricted ordinal intervals, and well-founded novelty selection.
-/

namespace FunctorialGeometry

open CategoryTheory Limits Classical

/-! ##############################################################################
    PART I: CATEGORICAL FOUNDATIONS AND SUBMODULAR DEFECTS
    ##############################################################################

    SECTION 2: POSETS AND SUBOBJECT LATTICES AS THIN CATEGORIES
    ============================================================================== -/

section ThinBasics

variable {L : Type*} [PartialOrder L]

/-- In any poset category, every hom-set is a subsingleton. -/
theorem thin_hom_subsingleton (x y : L) : Subsingleton (x ⟶ y) :=
  inferInstance

/-- In a thin category, parallel morphisms are identical. -/
theorem thin_hom_unique (x y : L) (f g : x ⟶ y) : f = g :=
  Subsingleton.elim f g

/-- In a thin category, every morphism is automatically a monomorphism. -/
theorem thin_mono {x y : L} (f : x ⟶ y) : Mono f := by
  constructor
  intro z g h _
  exact Subsingleton.elim g h

/-- In a thin category, every morphism is automatically an epimorphism. -/
theorem thin_epi {x y : L} (f : x ⟶ y) : Epi f := by
  constructor
  intro z g h _
  exact Subsingleton.elim g h

/-- Any endomorphism in a thin category is the identity. -/
theorem thin_end_is_id (x : L) (f : x ⟶ x) : f = 𝟙 x :=
  Subsingleton.elim f (𝟙 x)

/-- Any extension with a retraction in a thin category splits trivially. -/
theorem thin_extension_splits {A B : L} (f : A ⟶ B) (p : B ⟶ A) :
    p ≫ f = 𝟙 B ∧ f ≫ p = 𝟙 A :=
  ⟨Subsingleton.elim (p ≫ f) (𝟙 B), Subsingleton.elim (f ≫ p) (𝟙 A)⟩

/-- Monotone map between posets is canonically a functor between thin categories. -/
def monotone_functor {M : Type*} [PartialOrder M] (F : L → M) (hF : Monotone F) :
    L ⥤ M where
  obj x := F x
  map {x y} f := homOfLE (hF (leOfHom f))

/-- The functor induced by a closure operator. -/
def ClosureOperator.toFunctor (C : ClosureOperator L) : L ⥤ L :=
  monotone_functor C C.monotone

/-- A closure operator naturally defines an idempotent Monad on the poset category. -/
def ClosureOperator.toMonad (C : ClosureOperator L) : CategoryTheory.Monad L where
  toFunctor := C.toFunctor
  η := {
    app := fun x => homOfLE (C.le_closure x)
    naturality := fun _ _ _ => thin_hom_unique _ _ _ _
  }
  μ := {
    app := fun x => homOfLE (le_of_eq (C.idempotent x))
    naturality := fun _ _ _ => thin_hom_unique _ _ _ _
  }
  assoc := fun _ => thin_hom_unique _ _ _ _
  left_unit := fun _ => thin_hom_unique _ _ _ _
  right_unit := fun _ => thin_hom_unique _ _ _ _

end ThinBasics

section LatticeUniversal

variable {Lat : Type*} [Lattice Lat]

/-- In a lattice category, meet x ⊓ y satisfies the universal product property. -/
theorem meet_le_left (x y : Lat) : (x ⊓ y : Lat) ≤ x := inf_le_left
theorem meet_le_right (x y : Lat) : (x ⊓ y : Lat) ≤ y := inf_le_right

theorem meet_universal {x y z : Lat} (hzx : z ≤ x) (hzy : z ≤ y) :
    z ≤ x ⊓ y :=
  le_inf hzx hzy

/-- In a lattice category, join x ⊔ y satisfies the universal coproduct property. -/
theorem le_join_left (x y : Lat) : x ≤ (x ⊔ y : Lat) := le_sup_left
theorem le_join_right (x y : Lat) : y ≤ (x ⊔ y : Lat) := le_sup_right

theorem join_universal {x y z : Lat} (hxz : x ≤ z) (hyz : y ≤ z) :
    x ⊔ y ≤ z :=
  sup_le hxz hyz

end LatticeUniversal

section SubobjectThin

variable {C : Type*} [Category C] (X : C)

/-- Subobject lattice Sub(X) is a thin category. -/
theorem subobject_is_thin (A B : Subobject X) : Subsingleton (A ⟶ B) :=
  inferInstance

theorem subobject_mono (A B : Subobject X) (f : A ⟶ B) : Mono f :=
  thin_mono f

theorem subobject_epi (A B : Subobject X) (f : A ⟶ B) : Epi f :=
  thin_epi f

end SubobjectThin

/-! ==============================================================================
    SECTION 3: SUBMODULAR DEFECTS AND MODULARITY
    ============================================================================== -/

section SubmodularDefect

variable {L : Type*} [Lattice L]

/-- A submodular rank function on a lattice L. -/
structure SubmodularRank (L : Type*) [Lattice L] where
  rk : L → ℤ
  submodular : ∀ A B : L, rk (A ⊔ B) + rk (A ⊓ B) ≤ rk A + rk B

/-- The Submodular Defect Δ(A, B) = (rk A + rk B) - (rk(A ⊔ B) + rk(A ⊓ B)). -/
def submodularDefect (R : SubmodularRank L) (A B : L) : ℤ :=
  (R.rk A + R.rk B) - (R.rk (A ⊔ B) + R.rk (A ⊓ B))

/-- The defect is strictly non-negative. -/
theorem defect_nonneg (R : SubmodularRank L) (A B : L) :
    0 ≤ submodularDefect R A B := by
  dsimp [submodularDefect]
  have h := R.submodular A B
  linarith

/-- The defect vanishes if and only if the modular equality holds on {A, B}. -/
theorem defect_zero_iff_modular (R : SubmodularRank L) (A B : L) :
    submodularDefect R A B = 0 ↔ R.rk (A ⊔ B) + R.rk (A ⊓ B) = R.rk A + R.rk B := by
  dsimp [submodularDefect]
  constructor <;> intro h <;> linarith

/-- A modular rank function where the defect vanishes everywhere. -/
structure ModularRank (L : Type*) [Lattice L] extends SubmodularRank L where
  modular : ∀ A B : L, rk (A ⊔ B) + rk (A ⊓ B) = rk A + rk B

theorem modular_defect_zero (M : ModularRank L) (A B : L) :
    submodularDefect M.toSubmodularRank A B = 0 := by
  rw [defect_zero_iff_modular]
  exact M.modular A B

/-- Meet interaction in thin categories playing the role of a zero-order product. -/
def meetInteraction (A B : L) : L := A ⊓ B

theorem meetInteraction_comm (A B : L) : meetInteraction A B = meetInteraction B A := by
  dsimp [meetInteraction]; rw [inf_comm]

theorem meetInteraction_assoc (A B C : L) : meetInteraction (meetInteraction A B) C = meetInteraction A (meetInteraction B C) := by
  dsimp [meetInteraction]; rw [inf_assoc]

theorem meetInteraction_universal {A B C : L} (hCA : C ≤ A) (hCB : C ≤ B) :
    C ≤ meetInteraction A B :=
  le_inf hCA hCB

end SubmodularDefect

/-! ##############################################################################
    PART III: PATH VALUATIONS AND CHAIN APPLICATIONS
    ##############################################################################

    SECTION 6: PATH VALUATIONS ON STEP SEQUENCES AND COVERING QUIVERS
    ============================================================================== -/

section TravelMonoid

/-- 2×2 upper-triangular unipotent matrix [[1, e], [0, 1]]. -/
@[ext]
structure Unipotent2 where
  e : ℤ
  deriving DecidableEq, Repr

namespace Unipotent2

def id : Unipotent2 := ⟨0⟩
def mul (m1 m2 : Unipotent2) : Unipotent2 := ⟨m1.e + m2.e⟩

instance : One Unipotent2 := ⟨id⟩
instance : Mul Unipotent2 := ⟨mul⟩

@[simp] theorem id_e : (1 : Unipotent2).e = 0 := rfl
@[simp] theorem mul_e (m1 m2 : Unipotent2) : (m1 * m2).e = m1.e + m2.e := rfl

theorem mul_assoc (a b c : Unipotent2) : (a * b) * c = a * (b * c) := by
  rcases a with ⟨a1⟩; rcases b with ⟨b1⟩; rcases c with ⟨c1⟩
  ext; change (a1 + b1) + c1 = a1 + (b1 + c1); omega

theorem one_mul (a : Unipotent2) : 1 * a = a := by
  rcases a with ⟨a1⟩; ext; change 0 + a1 = a1; omega

theorem mul_one (a : Unipotent2) : a * 1 = a := by
  rcases a with ⟨a1⟩; ext; change a1 + 0 = a1; omega

end Unipotent2

open Unipotent2

/-- The Travel Experience state: (action : ℕ, transport : Unipotent2). -/
@[ext]
structure TravelExperience where
  action : ℕ
  transport : Unipotent2
  deriving DecidableEq, Repr

namespace TravelExperience

def id : TravelExperience := ⟨0, 1⟩
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

theorem mul_assoc (a b c : TravelExperience) : (a * b) * c = a * (b * c) := by
  rcases a with ⟨a1, ⟨a2⟩⟩; rcases b with ⟨b1, ⟨b2⟩⟩; rcases c with ⟨c1, ⟨c2⟩⟩
  ext <;> [change (a1 + b1) + c1 = a1 + (b1 + c1); change (a2 + b2) + c2 = a2 + (b2 + c2)] <;> omega

theorem one_mul (a : TravelExperience) : 1 * a = a := by
  rcases a with ⟨a1, ⟨a2⟩⟩; ext <;> [change 0 + a1 = a1; change 0 + a2 = a2] <;> omega

theorem mul_one (a : TravelExperience) : a * 1 = a := by
  rcases a with ⟨a1, ⟨a2⟩⟩; ext <;> [change a1 + 0 = a1; change a2 + 0 = a2] <;> omega

end TravelExperience

open TravelExperience

variable {L : Type*} [PartialOrder L]

/-- An elementary step (`source ≤ target`) in the lattice, equipped with a cost and an assigned integer label (`defect`). -/
structure LatticeStep (L : Type*) [PartialOrder L] where
  source : L
  target : L
  le : source ≤ target
  friction_cost : ℕ
  defect : ℤ

/-- Functorial valuation of a lattice step into the travel monoid. -/
def stepExperience (s : LatticeStep L) : TravelExperience :=
  ⟨s.friction_cost, ⟨s.defect⟩⟩

/-- Path valuation composing a sequence of lattice steps into the travel monoid. -/
def pathExperience (p : List (LatticeStep L)) : TravelExperience :=
  p.foldl (fun acc s => acc * stepExperience s) 1

@[simp] theorem pathExperience_nil : pathExperience ([] : List (LatticeStep L)) = 1 := rfl

lemma foldl_stepExperience (l : List (LatticeStep L)) (init : TravelExperience) :
    l.foldl (fun acc s => acc * stepExperience s) init = init * pathExperience l := by
  induction l generalizing init with
  | nil =>
    dsimp [pathExperience]
    rw [TravelExperience.mul_one]
  | cons head tail ih =>
    change (tail.foldl (fun acc s => acc * stepExperience s) (init * stepExperience head)) =
      init * (tail.foldl (fun acc s => acc * stepExperience s) (1 * stepExperience head))
    rw [ih (init * stepExperience head)]
    rw [ih (1 * stepExperience head)]
    rw [TravelExperience.one_mul]
    rw [TravelExperience.mul_assoc]

/-- Path concatenation is homomorphic under path valuation. -/
theorem pathExperience_append (p q : List (LatticeStep L)) :
    pathExperience (p ++ q) = pathExperience p * pathExperience q := by
  dsimp [pathExperience]
  rw [List.foldl_append]
  rw [foldl_stepExperience]
  rfl

/-- Non-trivial steps strictly increase accumulated action. -/
theorem action_strictly_increases (t : TravelExperience) (s : LatticeStep L) (hcost : 0 < s.friction_cost) :
    t.action < (t * stepExperience s).action := by
  dsimp [stepExperience]; linarith

/-- The valuation of a nonempty step list starts with its first step. -/
@[simp] theorem pathExperience_cons (s : LatticeStep L) (p : List (LatticeStep L)) :
    pathExperience (s :: p) = stepExperience s * pathExperience p := by
  simpa [pathExperience, TravelExperience.one_mul] using
    pathExperience_append [s] p

/-- Total path cost is the sum of the assigned step costs. -/
theorem pathExperience_action (p : List (LatticeStep L)) :
    (pathExperience p).action = (p.map LatticeStep.friction_cost).sum := by
  induction p with
  | nil => rfl
  | cons s p ih => simp [ih, stepExperience]

/-- Total shear label is the sum of the assigned integer labels. -/
theorem pathExperience_label (p : List (LatticeStep L)) :
    (pathExperience p).transport.e = (p.map LatticeStep.defect).sum := by
  induction p with
  | nil => rfl
  | cons s p ih => simp [ih, stepExperience]

/-- Evaluate a binary bracket pattern by multiplying the valuations of its subpaths.
At each split, the left subtree consumes its number of leaves from the step list. -/
def evalBracketPath (p : List (LatticeStep L)) : BinaryTree Unit → TravelExperience
  | .nil => pathExperience (p.take 1)
  | .node _ a b =>
    evalBracketPath (p.take a.numLeaves) a * evalBracketPath (p.drop a.numLeaves) b

/-- Every bracket pattern of a step list evaluates to its ordinary path valuation. -/
theorem evalBracketPath_eq (t : BinaryTree Unit) (p : List (LatticeStep L))
    (hp : p.length = t.numLeaves) : evalBracketPath p t = pathExperience p := by
  induction t generalizing p with
  | nil =>
    simp only [BinaryTree.numLeaves] at hp
    simp [evalBracketPath, List.take_of_length_le (by omega : p.length ≤ 1)]
  | node u a b iha ihb =>
    have ha : (p.take a.numLeaves).length = a.numLeaves := by
      simp only [List.length_take]
      have h := hp
      simp only [BinaryTree.numLeaves] at h
      omega
    have hb : (p.drop a.numLeaves).length = b.numLeaves := by
      simp only [List.length_drop]
      simp only [BinaryTree.numLeaves] at hp
      omega
    rw [evalBracketPath, iha _ ha, ihb _ hb, ← pathExperience_append,
      List.take_append_drop]

/-- The labelled elementary step at index `i` of a finite monotone chain. -/
def chainStep {n : ℕ} (x : Fin (n + 1) → L) (hx : Monotone x)
    (cost : Fin n → ℕ) (label : Fin n → ℤ) (i : Fin n) : LatticeStep L where
  source := x i.castSucc
  target := x i.succ
  le := hx (show i.val ≤ i.val + 1 from Nat.le_succ i.val)
  friction_cost := cost i
  defect := label i

/-- The ordered list of all `n` labelled steps in a finite chain. -/
def chainSteps {n : ℕ} (x : Fin (n + 1) → L) (hx : Monotone x)
    (cost : Fin n → ℕ) (label : Fin n → ℤ) : List (LatticeStep L) :=
  List.ofFn (chainStep x hx cost label)

/-- The chain valuation consists of the finite sums of its costs and labels. -/
theorem chainSteps_valuation {n : ℕ} (x : Fin (n + 1) → L) (hx : Monotone x)
    (cost : Fin n → ℕ) (label : Fin n → ℤ) :
    pathExperience (chainSteps x hx cost label) = ⟨∑ i, cost i, ⟨∑ i, label i⟩⟩ := by
  ext <;> simp [pathExperience_action, pathExperience_label, chainSteps,
    List.map_ofFn, chainStep, List.sum_ofFn]

/-- Evaluate a full bracket pattern on the labelled steps of a fixed chain. -/
def evalChainPathBracketing {n : ℕ} (x : Fin (n + 1) → L) (hx : Monotone x)
    (cost : Fin n → ℕ) (label : Fin n → ℤ) (t : FullBracketing n) : TravelExperience :=
  evalBracketPath (chainSteps x hx cost label) t.val

/-- Each full pattern gives the fixed chain's total path valuation. -/
theorem evalChainPathBracketing_eq {n : ℕ} (x : Fin (n + 1) → L) (hx : Monotone x)
    (cost : Fin n → ℕ) (label : Fin n → ℤ) (t : FullBracketing n) :
    evalChainPathBracketing x hx cost label t = pathExperience (chainSteps x hx cost label) := by
  apply evalBracketPath_eq
  simp [chainSteps, t.property]

/-- Unit step costs count the arrows, for every full bracket pattern. -/
theorem evalChainPathBracketing_unit_cost {n : ℕ} (x : Fin (n + 1) → L)
    (hx : Monotone x) (label : Fin n → ℤ) (t : FullBracketing n) :
    (evalChainPathBracketing x hx (fun _ => 1) label t).action = n := by
  rw [evalChainPathBracketing_eq, chainSteps_valuation]
  simp

/-- For every arity, retained bracket patterns give the associahedral face order.
For a fixed labelled chain, all full patterns give the same arrow and path valuation. -/
theorem all_Kn_chain_path_valuations {n : ℕ} (x : Fin (n + 1) → L) (hx : Monotone x)
    (cost : Fin n → ℕ) (label : Fin n → ℤ) :
    Nonempty (KnBracketing n ≃o KnFace n) ∧
      ∀ s t : FullBracketing n,
        evalChainBracketing x hx s = evalChainBracketing x hx t ∧
        evalChainPathBracketing x hx cost label s = evalChainPathBracketing x hx cost label t := by
  refine ⟨⟨all_Kn_orderIso n⟩, fun s t => ⟨all_Kn_chain_composites x hx s t, ?_⟩⟩
  rw [evalChainPathBracketing_eq, evalChainPathBracketing_eq]

end TravelMonoid

/-! ==============================================================================
    SECTION 7: TRANSFINITE CELLULAR FILTRATIONS AND BASIS DISCOVERY
    ============================================================================== -/

section CellularFiltration

universe u
variable {A : Type (u+1)} [Category.{u} A] [Abelian A] [HasLimitsOfSize.{u, u} A] [HasColimitsOfSize.{u, u} A] [WellPowered.{u} A]
variable (U₀ : A)

noncomputable instance (priority := 2000) subobjectSupSet (X : A) : SupSet (Subobject X) :=
  ⟨Subobject.sSup.{u, u, u+1}⟩

noncomputable instance (priority := 2000) subobjectInfSet (X : A) : InfSet (Subobject X) :=
  ⟨Subobject.sInf.{u, u, u+1}⟩

noncomputable instance (priority := 2000) subobjectCompleteSemilatticeSup (X : A) : CompleteSemilatticeSup (Subobject X) :=
  Subobject.completeSemilatticeSup.{u, u, u+1}

noncomputable instance (priority := 2000) subobjectCompleteSemilatticeInf (X : A) : CompleteSemilatticeInf (Subobject X) :=
  Subobject.completeSemilatticeInf.{u, u, u+1}

noncomputable instance (priority := 2000) subobjectCompleteLattice (X : A) : CompleteLattice (Subobject X) :=
  Subobject.instCompleteLattice.{u, u, u+1}

def IsSimple (X : A) : Prop := 
  ¬ IsZero X ∧ ∀ (Y : Subobject X), Y = ⊥ ∨ Y = ⊤

noncomputable def residual (C : Subobject U₀) : A := 
  cokernel C.arrow

def IsSemiArtinian (U₀ : A) : Prop :=
  ∀ (C : Subobject U₀), ¬ IsZero (residual U₀ C) → 
    ∃ (a : A) (i : a ⟶ residual U₀ C), IsSimple a ∧ Mono i

lemma eq_top_of_isZero_residual (C : Subobject U₀) (h : IsZero (residual U₀ C)) : C = ⊤ := by
  have hπ : cokernel.π C.arrow = 0 := h.eq_zero_of_tgt _
  have : Epi C.arrow := Abelian.epi_of_cokernel_π_eq_zero C.arrow hπ
  have : IsIso C.arrow := isIso_of_mono_of_epi C.arrow
  exact Subobject.eq_top_of_isIso_arrow C

lemma not_isZero_residual_of_ne_top (C : Subobject U₀) (h : C ≠ ⊤) : ¬ IsZero (residual U₀ C) := by
  intro hz; exact h (eq_top_of_isZero_residual U₀ C hz)

lemma lt_cellular (C : Subobject U₀) (a : A) (i : a ⟶ cokernel C.arrow) (hi : Mono i) (ha : IsSimple a) :
    letI : Mono (pullback.snd i (cokernel.π C.arrow)) := pullback.snd_of_mono
    C < Subobject.mk (pullback.snd i (cokernel.π C.arrow)) := by
  have : Mono (pullback.snd i (cokernel.π C.arrow)) := pullback.snd_of_mono
  have h_le : C ≤ Subobject.mk (pullback.snd i (cokernel.π C.arrow)) := by
    have h_comm : (0 : (C : A) ⟶ a) ≫ i = C.arrow ≫ cokernel.π C.arrow := by
      rw [Limits.zero_comp, cokernel.condition]
    let g : (C : A) ⟶ pullback i (cokernel.π C.arrow) := pullback.lift 0 C.arrow h_comm
    have hg : g ≫ pullback.snd i (cokernel.π C.arrow) = C.arrow := pullback.lift_snd 0 C.arrow h_comm
    have := Subobject.mk_le_mk_of_comm g hg
    rwa [Subobject.mk_arrow] at this
  refine lt_of_le_not_ge h_le ?_
  intro h_ge
  let k : pullback i (cokernel.π C.arrow) ⟶ (C : A) := Subobject.ofMkLE (pullback.snd i (cokernel.π C.arrow)) C h_ge
  have hk : k ≫ C.arrow = pullback.snd i (cokernel.π C.arrow) := Subobject.ofMkLE_arrow _
  have h_comp : pullback.fst i (cokernel.π C.arrow) ≫ i = 0 := by
    calc pullback.fst i (cokernel.π C.arrow) ≫ i = pullback.snd i (cokernel.π C.arrow) ≫ cokernel.π C.arrow := pullback.condition
      _ = (k ≫ C.arrow) ≫ cokernel.π C.arrow := by rw [← hk]
      _ = k ≫ (C.arrow ≫ cokernel.π C.arrow) := by rw [Category.assoc]
      _ = k ≫ 0 := by rw [cokernel.condition]
      _ = 0 := Limits.comp_zero
  have h_fst_zero : pullback.fst i (cokernel.π C.arrow) = 0 := by
    rw [← cancel_mono i]; exact h_comp.trans Limits.zero_comp.symm
  have h_epi : Epi (pullback.fst i (cokernel.π C.arrow)) := inferInstance
  rw [h_fst_zero] at h_epi
  have : Epi (0 : pullback i (cokernel.π C.arrow) ⟶ a) := h_epi
  have h_zero : IsZero a := IsZero.of_epi_zero (pullback i (cokernel.π C.arrow)) a
  exact ha.1 h_zero

noncomputable def nextCellular (C : Subobject U₀) (h_semi : IsSemiArtinian U₀) : Subobject U₀ :=
  if h : IsZero (residual U₀ C) then C
  else
    let a := (h_semi C h).choose
    let i := (h_semi C h).choose_spec.choose
    haveI : Mono i := (h_semi C h).choose_spec.choose_spec.2
    haveI : Mono (pullback.snd i (cokernel.π C.arrow)) := pullback.snd_of_mono
    Subobject.mk (pullback.snd i (cokernel.π C.arrow))

lemma le_nextCellular (C : Subobject U₀) (h_semi : IsSemiArtinian U₀) :
    C ≤ nextCellular U₀ C h_semi := by
  dsimp [nextCellular]
  split_ifs with h
  · exact le_rfl
  · let a := (h_semi C h).choose
    let i := (h_semi C h).choose_spec.choose
    have ha_simple := (h_semi C h).choose_spec.choose_spec.1
    have hi : Mono i := (h_semi C h).choose_spec.choose_spec.2
    exact (lt_cellular U₀ C a i hi ha_simple).le

noncomputable def cellularSequence (h_semi : IsSemiArtinian U₀) (o : Ordinal.{u}) : Subobject U₀ :=
  Ordinal.limitRecOn o
    (⊥ : Subobject U₀)
    (fun _ C => nextCellular U₀ C h_semi)
    (fun a _ f => ⨆ (b : Ordinal.{u}) (hb : b < a), f b hb)

lemma le_iSup_subobject {ι : Sort*} (f : ι → Subobject U₀) (i : ι) :
    f i ≤ ⨆ j, f j :=
  le_sSup ⟨i, rfl⟩

lemma le_biSup_subobject (o : Ordinal.{u}) (o₁ : Ordinal.{u}) (h : o₁ < o)
    (f : (b : Ordinal.{u}) → b < o → Subobject U₀) :
    f o₁ h ≤ ⨆ (b : Ordinal.{u}) (hb : b < o), f b hb := by
  have h1 : f o₁ h ≤ ⨆ (hb : o₁ < o), f o₁ hb :=
    le_iSup_subobject U₀ (fun (hb : o₁ < o) => f o₁ hb) h
  have h2 : (⨆ (hb : o₁ < o), f o₁ hb) ≤ ⨆ (b : Ordinal.{u}) (hb : b < o), f b hb :=
    le_iSup_subobject U₀ (fun b => ⨆ (hb : b < o), f b hb) o₁
  exact h1.trans h2

lemma cellularSequence_limit (h_semi : IsSemiArtinian U₀) (o : Ordinal.{u}) (ho : Order.IsSuccLimit o) :
    cellularSequence U₀ h_semi o = ⨆ (b : Ordinal.{u}) (_hb : b < o), cellularSequence U₀ h_semi b := by
  dsimp [cellularSequence]
  exact Ordinal.limitRecOn_limit o _ _ _ ho

lemma cellularSequence_le (h_semi : IsSemiArtinian U₀) (o₁ o₂ : Ordinal.{u}) (h_le : o₁ ≤ o₂) :
    cellularSequence U₀ h_semi o₁ ≤ cellularSequence U₀ h_semi o₂ := by
  revert o₁
  induction o₂ using Ordinal.limitRecOn with
  | zero =>
    intro o₁ h₁
    have : o₁ = 0 := le_zero_iff.mp h₁
    subst this
    exact le_rfl
  | add_one o₂ ih =>
    intro o₁ h₁
    rcases eq_or_lt_of_le h₁ with rfl | hlt
    · exact le_rfl
    · have h_le_o₂ : o₁ ≤ o₂ := by
        rwa [← Order.succ_eq_add_one, Order.lt_succ_iff] at hlt
      have ih_le := ih o₁ h_le_o₂
      have step_le : cellularSequence U₀ h_semi o₂ ≤ cellularSequence U₀ h_semi (o₂ + 1) := by
        dsimp [cellularSequence]
        rw [Ordinal.limitRecOn_add_one]
        exact le_nextCellular U₀ (cellularSequence U₀ h_semi o₂) h_semi
      exact ih_le.trans step_le
  | limit o₂ ho ih =>
    intro o₁ h₁
    rcases eq_or_lt_of_le h₁ with rfl | hlt
    · exact le_rfl
    · rw [cellularSequence_limit U₀ h_semi o₂ ho]
      exact le_biSup_subobject U₀ o₂ o₁ hlt (fun b _ => cellularSequence U₀ h_semi b)

lemma cellularSequence_mono (h_semi : IsSemiArtinian U₀) :
    Monotone (cellularSequence U₀ h_semi) :=
  fun _ _ h => cellularSequence_le U₀ h_semi _ _ h
lemma cellularSequence_step_exists (h_semi : IsSemiArtinian U₀) (o : Ordinal.{u})
    (h_ne : cellularSequence U₀ h_semi o ≠ ⊤) :
    ∃ (a : A) (i : a ⟶ residual U₀ (cellularSequence U₀ h_semi o)) (hi : Mono i),
      IsSimple a ∧
      cellularSequence U₀ h_semi (o + 1) = (
        haveI : Mono i := hi
        haveI : Mono (pullback.snd i (cokernel.π (cellularSequence U₀ h_semi o).arrow)) := pullback.snd_of_mono
        Subobject.mk (pullback.snd i (cokernel.π (cellularSequence U₀ h_semi o).arrow))) := by
  have h_succ : cellularSequence U₀ h_semi (o + 1) = nextCellular U₀ (cellularSequence U₀ h_semi o) h_semi := by
    dsimp [cellularSequence]; rw [Ordinal.limitRecOn_add_one]
  have hz : ¬ IsZero (residual U₀ (cellularSequence U₀ h_semi o)) :=
    not_isZero_residual_of_ne_top U₀ _ h_ne
  let a := (h_semi (cellularSequence U₀ h_semi o) hz).choose
  let i := (h_semi (cellularSequence U₀ h_semi o) hz).choose_spec.choose
  have ha_simple := (h_semi (cellularSequence U₀ h_semi o) hz).choose_spec.choose_spec.1
  have hi : Mono i := (h_semi (cellularSequence U₀ h_semi o) hz).choose_spec.choose_spec.2
  refine ⟨a, i, hi, ha_simple, ?_⟩
  rw [h_succ]
  dsimp [nextCellular]
  rw [dif_neg hz]

lemma cellularSequence_strict_mono (h_semi : IsSemiArtinian U₀) (o : Ordinal.{u}) :
    cellularSequence U₀ h_semi o ≠ ⊤ → 
    cellularSequence U₀ h_semi o < cellularSequence U₀ h_semi (o + 1) := by
  intro h_ne
  have h_succ : cellularSequence U₀ h_semi (o + 1) = nextCellular U₀ (cellularSequence U₀ h_semi o) h_semi := by
    dsimp [cellularSequence]; rw [Ordinal.limitRecOn_add_one]
  rw [h_succ]
  have hz : ¬ IsZero (residual U₀ (cellularSequence U₀ h_semi o)) :=
    not_isZero_residual_of_ne_top U₀ _ h_ne
  dsimp [nextCellular]; rw [dif_neg hz]
  let a := (h_semi (cellularSequence U₀ h_semi o) hz).choose
  let i := (h_semi (cellularSequence U₀ h_semi o) hz).choose_spec.choose
  have ha_simple := (h_semi (cellularSequence U₀ h_semi o) hz).choose_spec.choose_spec.1
  have hi : Mono i := (h_semi (cellularSequence U₀ h_semi o) hz).choose_spec.choose_spec.2
  exact lt_cellular U₀ _ a i hi ha_simple

theorem cellular_eventuallyConst (f : Ordinal.{u} → Subobject U₀) (hf : Monotone f) :
    Filter.EventuallyConst f Filter.atTop := by
  have : Small.{u} (Subobject U₀) := inferInstance
  let e := equivShrink (Subobject U₀)
  let _ : PartialOrder (Shrink (Subobject U₀)) := PartialOrder.lift e.symm (Equiv.injective _)
  let f' : Ordinal.{u} → Shrink (Subobject U₀) := fun o => e (f o)
  have hf' : Monotone f' := fun a b hab => by
    change e.symm (e (f a)) ≤ e.symm (e (f b))
    simp only [Equiv.symm_apply_apply]
    exact hf hab
  have h_ev' := Ordinal.eventuallyConst_of_monotone hf'
  rw [Filter.eventuallyConst_atTop] at h_ev' ⊢
  rcases h_ev' with ⟨i, hi⟩
  refine ⟨i, fun j hj => ?_⟩
  have hj' := hi j hj
  dsimp [f'] at hj'
  have := congr_arg e.symm hj'
  simpa only [Equiv.symm_apply_apply] using this

lemma cellularSequence_stabilizes (h_semi : IsSemiArtinian U₀) :
    ∃ (Ω : Ordinal.{u}), cellularSequence U₀ h_semi Ω = cellularSequence U₀ h_semi (Ω + 1) := by
  have h_ev := cellular_eventuallyConst U₀ (cellularSequence U₀ h_semi) (cellularSequence_mono U₀ h_semi)
  rw [Filter.eventuallyConst_atTop] at h_ev
  rcases h_ev with ⟨Ω, hΩ⟩
  refine ⟨Ω, ?_⟩
  have h_le : Ω ≤ Ω + 1 := le_self_add
  exact (hΩ (Ω + 1) h_le).symm

/-- Transfinite Cellular Length Existence Theorem. -/
theorem cellular_length_exists (h_semi : IsSemiArtinian U₀) : 
    ∃ (Ω : Ordinal.{u}), cellularSequence U₀ h_semi Ω = ⊤ := by
  obtain ⟨Ω, hΩ⟩ := cellularSequence_stabilizes U₀ h_semi
  refine ⟨Ω, ?_⟩
  by_contra h_ne
  have h_lt := cellularSequence_strict_mono U₀ h_semi Ω h_ne
  rw [hΩ] at h_lt
  exact lt_irrefl _ h_lt

noncomputable def cellularLength (h_semi : IsSemiArtinian U₀) : Ordinal.{u} :=
  (cellular_length_exists U₀ h_semi).choose

theorem reconstruction (h_semi : IsSemiArtinian U₀) :
    cellularSequence U₀ h_semi (cellularLength U₀ h_semi) = ⊤ :=
  (cellular_length_exists U₀ h_semi).choose_spec

theorem reconstruction_iso (h_semi : IsSemiArtinian U₀) :
    IsIso (cellularSequence U₀ h_semi (cellularLength U₀ h_semi)).arrow := by
  rw [reconstruction]
  exact Subobject.top_arrow_isIso

def OrdinalInterval (Ω : Ordinal.{u}) : Type u := Shrink.{u} (Set.Iic Ω)

namespace OrdinalInterval

variable (Ω : Ordinal.{u})

noncomputable def toIic (x : OrdinalInterval Ω) : Set.Iic Ω :=
  (equivShrink (Set.Iic Ω)).symm x

noncomputable def ofIic (x : Set.Iic Ω) : OrdinalInterval Ω :=
  (equivShrink (Set.Iic Ω)) x

noncomputable instance : PartialOrder (OrdinalInterval Ω) :=
  PartialOrder.lift (toIic Ω) (Equiv.injective _)

noncomputable instance : Category (OrdinalInterval Ω) := inferInstance

noncomputable instance : IsFiltered (OrdinalInterval Ω) where
  nonempty := ⟨ofIic Ω ⟨⊥, Set.mem_Iic.mpr bot_le⟩⟩
  cocone_objs x y :=
    let m : Set.Iic Ω := ⟨max (toIic Ω x).1 (toIic Ω y).1, Set.mem_Iic.mpr (max_le (toIic Ω x).2 (toIic Ω y).2)⟩
    ⟨ofIic Ω m,
     homOfLE (show x ≤ ofIic Ω m by change (toIic Ω x).1 ≤ (toIic Ω (ofIic Ω m)).1; simp only [toIic, ofIic, Equiv.symm_apply_apply, Subtype.coe_le_coe]; exact le_max_left _ _),
     homOfLE (show y ≤ ofIic Ω m by change (toIic Ω y).1 ≤ (toIic Ω (ofIic Ω m)).1; simp only [toIic, ofIic, Equiv.symm_apply_apply, Subtype.coe_le_coe]; exact le_max_right _ _),
     trivial⟩
  cocone_maps {x y} f g := ⟨y, 𝟙 y, Subsingleton.elim _ _⟩

end OrdinalInterval

-- Transfinite Filtration functor and residual diagram
variable {J : Type u} [Category.{u} J]

noncomputable def residualDiagramMap (F : J ⥤ Subobject U₀) (j k : J) (f : j ⟶ k) : 
    cokernel (F.obj j).arrow ⟶ cokernel (F.obj k).arrow :=
  cokernel.desc (F.obj j).arrow (cokernel.π (F.obj k).arrow) (by 
    rw [← Subobject.ofLE_arrow (leOfHom (F.map f)), Category.assoc, cokernel.condition, comp_zero]
  )

noncomputable def residualDiagram (F : J ⥤ Subobject U₀) : J ⥤ A where
  obj j := cokernel (F.obj j).arrow
  map f := residualDiagramMap U₀ F _ _ f
  map_id j := by ext; simp [residualDiagramMap]
  map_comp f g := by ext; simp [residualDiagramMap]

def Convergence (F : J ⥤ Subobject U₀) : Prop :=
  ∃ (Ω : J), F.obj Ω = ⊤

/-- Vanishing of the residual colimit: directed colimit of residual cokernels vanishes. -/
theorem residual_colimit_vanishes (F : J ⥤ Subobject U₀) [IsFiltered J] (h_conv : Convergence U₀ F) :
    IsZero (colimit (residualDiagram U₀ F)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext j
  rw [Category.comp_id, comp_zero]
  rcases h_conv with ⟨Ω, hΩ⟩
  let k := IsFiltered.max j Ω
  let f := IsFiltered.leftToMax j Ω
  let g := IsFiltered.rightToMax j Ω
  have h_top : F.obj k = ⊤ := top_unique (hΩ ▸ leOfHom (F.map g))
  have h_zero : IsZero (cokernel (F.obj k).arrow) := by
    rw [h_top]
    apply isZero_cokernel_of_epi
  have eq1 : colimit.ι (residualDiagram U₀ F) j = (residualDiagram U₀ F).map f ≫ colimit.ι (residualDiagram U₀ F) k := by
    exact (colimit.w (residualDiagram U₀ F) f).symm
  rw [eq1]
  have h_iota_zero : colimit.ι (residualDiagram U₀ F) k = 0 := by
    apply IsZero.eq_of_src h_zero
  rw [h_iota_zero, comp_zero]

noncomputable def cellularIntervalFunctor (h_semi : IsSemiArtinian U₀) (Ω : Ordinal.{u}) :
    OrdinalInterval Ω ⥤ Subobject U₀ where
  obj x := cellularSequence U₀ h_semi (OrdinalInterval.toIic Ω x).1
  map {x y} f := homOfLE (by
    have : x ≤ y := leOfHom f
    exact cellularSequence_le U₀ h_semi _ _ this)

theorem cellular_residual_colimit_vanishes (h_semi : IsSemiArtinian U₀) :
    IsZero (colimit (residualDiagram U₀ (cellularIntervalFunctor U₀ h_semi (cellularLength U₀ h_semi)))) := by
  apply residual_colimit_vanishes
  refine ⟨OrdinalInterval.ofIic _ ⟨cellularLength U₀ h_semi, Set.mem_Iic.mpr le_rfl⟩, ?_⟩
  dsimp [cellularIntervalFunctor, OrdinalInterval.toIic, OrdinalInterval.ofIic]
  simp only [Equiv.symm_apply_apply]
  exact reconstruction U₀ h_semi

section CellularSES

variable (C : Subobject U₀) (a : A) (i : a ⟶ cokernel C.arrow) [Mono i]

lemma cellular_comm : (0 : (C : A) ⟶ a) ≫ i = C.arrow ≫ cokernel.π C.arrow := by
  rw [Limits.zero_comp, cokernel.condition]

/-- Canonical inclusion morphism from subobject `C` into the cellular pullback object. -/
noncomputable def cellularInclusion : (C : A) ⟶ pullback i (cokernel.π C.arrow) :=
  pullback.lift 0 C.arrow (cellular_comm U₀ C a i)

/-- Canonical projection morphism from the cellular pullback object onto simple layer `a`. -/
noncomputable def cellularProjection : pullback i (cokernel.π C.arrow) ⟶ a :=
  pullback.fst i (cokernel.π C.arrow)

@[simp]
lemma cellularInclusion_fst :
    cellularInclusion U₀ C a i ≫ pullback.fst i (cokernel.π C.arrow) = 0 := by
  dsimp [cellularInclusion]
  exact pullback.lift_fst 0 C.arrow (cellular_comm U₀ C a i)

@[simp]
lemma cellularInclusion_snd :
    cellularInclusion U₀ C a i ≫ pullback.snd i (cokernel.π C.arrow) = C.arrow := by
  dsimp [cellularInclusion]
  exact pullback.lift_snd 0 C.arrow (cellular_comm U₀ C a i)

lemma cellularInclusion_comp_projection :
    cellularInclusion U₀ C a i ≫ cellularProjection U₀ C a i = 0 :=
  cellularInclusion_fst U₀ C a i

instance : Mono (cellularInclusion U₀ C a i) := by
  have hg := cellularInclusion_snd U₀ C a i
  have : Mono C.arrow := C.arrow_mono
  exact mono_of_mono_fac hg

instance : Epi (cellularProjection U₀ C a i) := by
  dsimp [cellularProjection]
  infer_instance

/-- The short complex `C ⟶ pullback i (cokernel.π C.arrow) ⟶ a`. -/
noncomputable def cellularShortComplex : ShortComplex A :=
  ShortComplex.mk (cellularInclusion U₀ C a i) (cellularProjection U₀ C a i)
    (cellularInclusion_comp_projection U₀ C a i)

lemma coker_snd_comp_coker (s : KernelFork (cellularProjection U₀ C a i)) :
    (s.ι ≫ pullback.snd i (cokernel.π C.arrow)) ≫ cokernel.π C.arrow = 0 := by
  calc
    (s.ι ≫ pullback.snd i (cokernel.π C.arrow)) ≫ cokernel.π C.arrow
      = s.ι ≫ (pullback.snd i (cokernel.π C.arrow) ≫ cokernel.π C.arrow) := by rw [Category.assoc]
    _ = s.ι ≫ (pullback.fst i (cokernel.π C.arrow) ≫ i) := by rw [pullback.condition]
    _ = (s.ι ≫ pullback.fst i (cokernel.π C.arrow)) ≫ i := by rw [← Category.assoc]
    _ = (s.ι ≫ cellularProjection U₀ C a i) ≫ i := rfl
    _ = 0 ≫ i := by rw [KernelFork.condition s]
    _ = 0 := zero_comp

noncomputable def cellularLift (s : KernelFork (cellularProjection U₀ C a i))
    (h_coker_isLimit : IsLimit (KernelFork.ofι C.arrow (cokernel.condition C.arrow))) :
    s.pt ⟶ (C : A) :=
  h_coker_isLimit.lift (KernelFork.ofι (s.ι ≫ pullback.snd i (cokernel.π C.arrow)) (coker_snd_comp_coker U₀ C a i s))

lemma cellularLift_fac (s : KernelFork (cellularProjection U₀ C a i))
    (h_coker_isLimit : IsLimit (KernelFork.ofι C.arrow (cokernel.condition C.arrow))) :
    cellularLift U₀ C a i s h_coker_isLimit ≫ cellularInclusion U₀ C a i = s.ι := by
  have hu : cellularLift U₀ C a i s h_coker_isLimit ≫ C.arrow = s.ι ≫ pullback.snd i (cokernel.π C.arrow) :=
    h_coker_isLimit.fac (KernelFork.ofι (s.ι ≫ pullback.snd i (cokernel.π C.arrow)) (coker_snd_comp_coker U₀ C a i s)) WalkingParallelPair.zero
  apply pullback.hom_ext
  · simp only [Category.assoc, cellularInclusion_fst, comp_zero]
    exact (KernelFork.condition s).symm
  · simp only [Category.assoc, cellularInclusion_snd]
    exact hu

lemma cellularLift_uniq (s : KernelFork (cellularProjection U₀ C a i))
    (h_coker_isLimit : IsLimit (KernelFork.ofι C.arrow (cokernel.condition C.arrow)))
    (m : s.pt ⟶ (C : A)) (hm : m ≫ cellularInclusion U₀ C a i = s.ι) :
    m = cellularLift U₀ C a i s h_coker_isLimit := by
  have hm_coker : m ≫ C.arrow = s.ι ≫ pullback.snd i (cokernel.π C.arrow) := by
    calc
      m ≫ C.arrow = m ≫ (cellularInclusion U₀ C a i ≫ pullback.snd i (cokernel.π C.arrow)) := by rw [cellularInclusion_snd]
      _ = (m ≫ cellularInclusion U₀ C a i) ≫ pullback.snd i (cokernel.π C.arrow) := by rw [Category.assoc]
      _ = s.ι ≫ pullback.snd i (cokernel.π C.arrow) := by rw [hm]
  have hu : cellularLift U₀ C a i s h_coker_isLimit ≫ C.arrow = s.ι ≫ pullback.snd i (cokernel.π C.arrow) :=
    h_coker_isLimit.fac (KernelFork.ofι (s.ι ≫ pullback.snd i (cokernel.π C.arrow)) (coker_snd_comp_coker U₀ C a i s)) WalkingParallelPair.zero
  have h_eq : m ≫ C.arrow = cellularLift U₀ C a i s h_coker_isLimit ≫ C.arrow := by rw [hm_coker, hu]
  have : Mono C.arrow := C.arrow_mono
  exact (cancel_mono C.arrow).mp h_eq

/-- The kernel fork of the cellular projection is a limit cone, showing that the kernel
    of `cellularProjection` is canonically isomorphic to `C`. -/
noncomputable def isLimitCellularKernelFork :
    IsLimit (KernelFork.ofι (cellularInclusion U₀ C a i) (cellularInclusion_comp_projection U₀ C a i)) := by
  have h_coker_isLimit : IsLimit (KernelFork.ofι C.arrow (cokernel.condition C.arrow)) :=
    Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ (cokernel.π C.arrow) (cokernel.condition C.arrow))
      (cokernelIsCokernel C.arrow)
  exact Fork.IsLimit.mk _
    (fun s => cellularLift U₀ C a i s h_coker_isLimit)
    (fun s => cellularLift_fac U₀ C a i s h_coker_isLimit)
    (fun s m hm => cellularLift_uniq U₀ C a i s h_coker_isLimit m hm)

/-- The sequence `0 ⟶ C ⟶ pullback ⟶ a ⟶ 0` is exact. -/
theorem cellular_exact :
    (cellularShortComplex U₀ C a i).Exact :=
  ShortComplex.exact_of_f_is_kernel (cellularShortComplex U₀ C a i) (isLimitCellularKernelFork U₀ C a i)

instance : Mono (cellularShortComplex U₀ C a i).f := by
  dsimp [cellularShortComplex]
  infer_instance

instance : Epi (cellularShortComplex U₀ C a i).g := by
  dsimp [cellularShortComplex]
  infer_instance

/-- Main Cellular Extension Theorem: Every cellular step forms a Short Exact Sequence,
    presenting a length-1 extension `0 ⟶ C ⟶ pullback ⟶ a ⟶ 0`. -/
theorem cellular_shortExact :
    (cellularShortComplex U₀ C a i).ShortExact where
  exact := cellular_exact U₀ C a i

end CellularSES

end CellularFiltration

section BasisDiscovery

variable {L : Type} [CompleteLattice L]
variable {J : Type} [LinearOrder J] [WellFoundedLT J]
variable (embed : J → L)

class IsGenerated {L J : Type} [CompleteLattice L] (embed : J → L) : Prop where
  eq_iSup : ∀ x : L, x = ⨆ (j : J) (_ : embed j ≤ x), embed j

variable [IsGenerated embed]

lemma candidates_nonempty (x : L) (h : x < ⊤) : { j : J | ¬ (embed j ≤ x) }.Nonempty := by
  by_contra h_contra
  rw [Set.not_nonempty_iff_eq_empty] at h_contra
  have h_all : ∀ j, embed j ≤ x := by
    intro j; by_contra h_not_le; have h_in : j ∈ { j : J | ¬ (embed j ≤ x) } := h_not_le
    rw [h_contra] at h_in; exact h_in
  have h_top_le_x : (⊤ : L) ≤ x := by
    have h_top := IsGenerated.eq_iSup (embed := embed) ⊤
    rw [h_top]; apply iSup_le; intro j; apply iSup_le; intro _; exact h_all j
  exact h.ne (top_le_iff.mp h_top_le_x)

/-- Greedy choice function selecting the minimal uncovered generator. -/
noncomputable def fixedPriorityPhi (x : L) (h : x < ⊤) : J :=
  let candidates := { j : J | ¬ (embed j ≤ x) }
  have h_nonempty : candidates.Nonempty := candidates_nonempty embed x h
  WellFounded.min wellFounded_lt candidates h_nonempty

theorem novelty_of_fixedPriorityPhi (x : L) (h : x < ⊤) :
    ¬ (embed (fixedPriorityPhi embed x h) ≤ x) :=
  WellFounded.min_mem wellFounded_lt { j : J | ¬ (embed j ≤ x) } (candidates_nonempty embed x h)

/-- The transfinite sequence of extracted generators across ordinals. -/
noncomputable def xSeq (o : Ordinal) : L :=
  Ordinal.limitRecOn o
    (⊥ : L)
    (fun _ x => if h : x < ⊤ then x ⊔ embed (fixedPriorityPhi embed x h) else x)
    (fun a _ f => ⨆ (b : Ordinal) (hb : b < a), f b hb)

/-- The final supremum of all generators extracted across the transfinite sequence. -/
noncomputable def sieveOutput : L :=
  ⨆ (o : Ordinal.{0}), xSeq embed o

theorem xSeq_zero : xSeq embed 0 = ⊥ :=
  Ordinal.limitRecOn_zero _ _ _

theorem xSeq_add_one (o : Ordinal) :
    xSeq embed (o + 1) = if h : xSeq embed o < ⊤ then xSeq embed o ⊔ embed (fixedPriorityPhi embed (xSeq embed o) h) else xSeq embed o := by
  dsimp [xSeq]
  rw [Ordinal.limitRecOn_add_one]
  rfl

lemma xSeq_le (o₁ o₂ : Ordinal.{0}) (h : o₁ ≤ o₂) : xSeq embed o₁ ≤ xSeq embed o₂ := by
  revert o₁
  induction o₂ using Ordinal.limitRecOn with
  | zero =>
    intro o₁ h₁
    have : o₁ = 0 := le_zero_iff.mp h₁
    subst this
    exact le_rfl
  | add_one o₂ ih =>
    intro o₁ h₁
    rcases eq_or_lt_of_le h₁ with rfl | hlt
    · exact le_rfl
    · have h_le_o₂ : o₁ ≤ o₂ := by
        rwa [← Order.succ_eq_add_one, Order.lt_succ_iff] at hlt
      have ih_le := ih o₁ h_le_o₂
      have step_le : xSeq embed o₂ ≤ xSeq embed (o₂ + 1) := by
        rw [xSeq_add_one]
        split_ifs
        · exact le_sup_left
        · exact le_rfl
      exact ih_le.trans step_le
  | limit o₂ ho ih =>
    intro o₁ h₁
    rcases eq_or_lt_of_le h₁ with rfl | hlt
    · exact le_rfl
    · have : xSeq embed o₂ = ⨆ (b : Ordinal) (hb : b < o₂), xSeq embed b := by
        dsimp [xSeq]; exact Ordinal.limitRecOn_limit o₂ _ _ _ ho
      rw [this]
      have h1 : xSeq embed o₁ ≤ ⨆ (hb : o₁ < o₂), xSeq embed o₁ := le_iSup (fun _ => xSeq embed o₁) hlt
      have h2 : (⨆ (hb : o₁ < o₂), xSeq embed o₁) ≤ ⨆ (b : Ordinal) (hb : b < o₂), xSeq embed b := le_iSup_of_le o₁ (by rfl)
      exact h1.trans h2

lemma xSeq_strict_mono (o : Ordinal.{0}) (h : xSeq embed o < ⊤) : xSeq embed o < xSeq embed (o + 1) := by
  have h_succ : xSeq embed (o + 1) = xSeq embed o ⊔ embed (fixedPriorityPhi embed (xSeq embed o) h) := by
    rw [xSeq_add_one, dif_pos h]
  rw [h_succ]
  refine lt_of_le_not_ge le_sup_left ?_
  intro h_ge
  have : embed (fixedPriorityPhi embed (xSeq embed o) h) ≤ xSeq embed o := le_trans le_sup_right h_ge
  exact novelty_of_fixedPriorityPhi embed (xSeq embed o) h this

theorem sieveOutput_eq_top : sieveOutput embed = ⊤ := by
  have hf : Monotone (xSeq embed) := fun _ _ h => xSeq_le embed _ _ h
  have : Small.{0} L := inferInstance
  let e := equivShrink L
  let _ : PartialOrder (Shrink L) := PartialOrder.lift e.symm (Equiv.injective _)
  let f' : Ordinal.{0} → Shrink L := fun o => e (xSeq embed o)
  have hf' : Monotone f' := fun a b hab => by
    change e.symm (e (xSeq embed a)) ≤ e.symm (e (xSeq embed b))
    simp only [Equiv.symm_apply_apply]
    exact hf hab
  have h_ev' := Ordinal.eventuallyConst_of_monotone hf'
  rw [Filter.eventuallyConst_atTop] at h_ev'
  rcases h_ev' with ⟨Ω, hΩ⟩
  have h_stab : xSeq embed Ω = xSeq embed (Ω + 1) := by
    have h2 := hΩ (Ω + 1) le_self_add
    dsimp [f'] at h2
    apply_fun e.symm at h2
    simp only [Equiv.symm_apply_apply] at h2
    exact h2.symm
  by_contra h_ne
  have h_lt : xSeq embed Ω < xSeq embed (Ω + 1) := xSeq_strict_mono embed Ω (lt_top_iff_ne_top.mpr (by
    intro h_eq
    have h_le_sieve : xSeq embed Ω ≤ sieveOutput embed := le_iSup (fun o => xSeq embed o) Ω
    rw [h_eq] at h_le_sieve
    exact h_ne (top_le_iff.mp h_le_sieve)
  ))
  rw [h_stab] at h_lt
  exact lt_irrefl _ h_lt

/-- Every transfinite stage is bounded above by the sieve output. -/
theorem xSeq_le_sieveOutput (o : Ordinal.{0}) : xSeq embed o ≤ sieveOutput embed :=
  le_iSup (fun o => xSeq embed o) o

/-- The sieve output is the least upper bound of the transfinite sequence. -/
theorem sieveOutput_is_lub (x : L) : sieveOutput embed ≤ x ↔ ∀ (o : Ordinal.{0}), xSeq embed o ≤ x :=
  iSup_le_iff

end BasisDiscovery

/-! ##############################################################################
    PART II: HIGHER ASSOCIATIVITY, ASSOCIAHEDRA, AND ROOT GEOMETRY
    ##############################################################################

    SECTION 4: HIGHER ASSOCIATIVITY, ASSOCIAHEDRA, AND ROOT LABELS
    ============================================================================== -/

section AssociahedraDuality

/-- The 1 parenthesization of 2 letters (vertex of Tamari 𝒯₂ / Stasheff K₂ = 0D point). -/
inductive Tree2 : Type
  | t1 : Tree2 -- (ab)
  deriving DecidableEq, Repr

instance : Fintype Tree2 where
  elems := {Tree2.t1}
  complete := by intro x; cases x; simp

theorem tamari2_card : Fintype.card Tree2 = 1 := rfl

/-- The 2 parenthesizations of 3 letters (vertices of Tamari 𝒯₃ / Stasheff K₃ = 1D interval). -/
inductive Tree3 : Type
  | t1 : Tree3 -- ((ab)c)
  | t2 : Tree3 -- (a(bc))
  deriving DecidableEq, Repr

def tamari3_le : Tree3 → Tree3 → Prop
  | Tree3.t1, _ => True
  | Tree3.t2, Tree3.t2 => True
  | _, _ => False

instance : LE Tree3 where le := tamari3_le

instance : PartialOrder Tree3 where
  le := tamari3_le
  le_refl := by intro x; cases x <;> trivial
  le_trans := by intro a b c; cases a <;> cases b <;> cases c <;> simp [tamari3_le]
  le_antisymm := by intro a b; cases a <;> cases b <;> simp [tamari3_le]

instance : Fintype Tree3 where
  elems := {Tree3.t1, Tree3.t2}
  complete := by intro x; cases x <;> simp

theorem tamari3_card : Fintype.card Tree3 = 2 := rfl

/-- The 5 parenthesizations of 4 letters (vertices of Tamari 𝒯₄ / Stasheff K₄). -/
inductive Tree4 : Type
  | t1 : Tree4 -- ((ab)c)d
  | t2 : Tree4 -- (a(bc))d
  | t3 : Tree4 -- (ab)(cd)
  | t4 : Tree4 -- a((bc)d)
  | t5 : Tree4 -- a(b(cd))
  deriving DecidableEq, Repr

open Tree4

def tamari_le : Tree4 → Tree4 → Prop
  | t1, _ => True
  | t2, t2 => True | t2, t4 => True | t2, t5 => True
  | t3, t3 => True | t3, t5 => True
  | t4, t4 => True | t4, t5 => True
  | t5, t5 => True
  | _, _ => False

instance : LE Tree4 where le := tamari_le

theorem tamari_refl (t : Tree4) : t ≤ t := by cases t <;> trivial
theorem tamari_trans (a b c : Tree4) : a ≤ b → b ≤ c → a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp [LE.le, tamari_le]
theorem tamari_antisymm (a b : Tree4) : a ≤ b → b ≤ a → a = b := by
  cases a <;> cases b <;> simp [LE.le, tamari_le]

instance : PartialOrder Tree4 where
  le := tamari_le
  le_refl := tamari_refl
  le_trans := tamari_trans
  le_antisymm := tamari_antisymm

def tamari_sup : Tree4 → Tree4 → Tree4
  | t1, x => x
  | x, t1 => x
  | t5, _ => t5
  | _, t5 => t5
  | t2, t2 => t2
  | t2, t3 => t5
  | t2, t4 => t4
  | t3, t2 => t5
  | t3, t3 => t3
  | t3, t4 => t5
  | t4, t2 => t4
  | t4, t3 => t5
  | t4, t4 => t4

def tamari_inf : Tree4 → Tree4 → Tree4
  | t1, _ => t1
  | _, t1 => t1
  | t5, x => x
  | x, t5 => x
  | t2, t2 => t2
  | t2, t3 => t1
  | t2, t4 => t2
  | t3, t2 => t1
  | t3, t3 => t3
  | t3, t4 => t1
  | t4, t2 => t2
  | t4, t3 => t1
  | t4, t4 => t4

instance : Lattice Tree4 where
  sup := tamari_sup
  le_sup_left := by intro a b; cases a <;> cases b <;> simp [tamari_sup, LE.le, tamari_le]
  le_sup_right := by intro a b; cases a <;> cases b <;> simp [tamari_sup, LE.le, tamari_le]
  sup_le := by intro a b c; cases a <;> cases b <;> cases c <;> simp [tamari_sup, LE.le, tamari_le]
  inf := tamari_inf
  inf_le_left := by intro a b; cases a <;> cases b <;> simp [tamari_inf, LE.le, tamari_le]
  inf_le_right := by intro a b; cases a <;> cases b <;> simp [tamari_inf, LE.le, tamari_le]
  le_inf := by intro a b c; cases a <;> cases b <;> cases c <;> simp [tamari_inf, LE.le, tamari_le]

inductive RightRot : Tree4 → Tree4 → Prop
  | t1_t2 : RightRot t1 t2
  | t1_t3 : RightRot t1 t3
  | t2_t4 : RightRot t2 t4
  | t3_t5 : RightRot t3 t5
  | t4_t5 : RightRot t4 t5

theorem rightRot_le {a b : Tree4} (h : RightRot a b) : a ≤ b := by
  cases h <;> simp [LE.le, tamari_le]

open Relation

theorem tamari_le_eq_reflTransGen :
    (· ≤ ·) = ReflTransGen RightRot (α := Tree4) := by
  ext a b
  constructor
  · intro h
    cases a <;> cases b <;> first | exact .refl | (revert h; exact fun _ => by contradiction) | skip
    · exact .tail .refl .t1_t2
    · exact .tail .refl .t1_t3
    · exact .tail (.tail .refl .t1_t2) .t2_t4
    · exact .tail (.tail .refl .t1_t3) .t3_t5
    · exact .tail .refl .t2_t4
    · exact .tail (.tail .refl .t2_t4) .t4_t5
    · exact .tail .refl .t3_t5
    · exact .tail .refl .t4_t5
  · intro h
    induction h with
    | refl => exact le_rfl
    | tail _ h2 ih => exact le_trans ih (rightRot_le h2)


instance : Fintype Tree4 where
  elems := {t1, t2, t3, t4, t5}
  complete := by intro x; cases x <;> simp

/-- Catalan C₃ = 5 vertices of Tamari 𝒯₄. -/
theorem tamari4_card : Fintype.card Tree4 = 5 := rfl

/-! ### Universal N-Dimensional Associahedron-Root Duality (K_{n+2} ≅ Aₙ) -/

/-- The almost-positive root system of type Aₙ for arbitrary rank n:
    - Positive roots α_{i..j} for 0 ≤ i ≤ j < n (cardinality n(n+1)/2)
    - Negative simple roots -α_k for 0 ≤ k < n (cardinality n) -/
inductive RootAn (n : ℕ) : Type
  | pos (i j : Fin n) (hle : i.val ≤ j.val) : RootAn n
  | neg_simple (k : Fin n) : RootAn n
  deriving DecidableEq

/-- A diagonal of a convex (n+3)-gon (vertices 0 to n+2) is a pair of vertices (a, b)
    such that a + 2 ≤ b and (a, b) ≠ (0, n+2). -/
@[ext]
structure Diagonal (n : ℕ) : Type where
  a : Fin (n + 3)
  b : Fin (n + 3)
  ha : a.val + 2 ≤ b.val
  h_not_base : ¬ (a.val = 0 ∧ b.val = n + 2)
  deriving DecidableEq

instance (n : ℕ) : Fintype (Diagonal n) :=
  Fintype.ofEquiv { p : Fin (n+3) × Fin (n+3) // p.1.val + 2 ≤ p.2.val ∧ ¬(p.1.val = 0 ∧ p.2.val = n+2) }
    { toFun := fun p => ⟨p.val.1, p.val.2, p.property.1, p.property.2⟩
      invFun := fun d => ⟨(d.a, d.b), d.ha, d.h_not_base⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun d => by cases d; rfl }

/-- The boundary facets of the (n+2)-associahedron K_{n+2} are combinatorial representations of the diagonals.
    We partition them into base chords and internal chords to match the root system. -/
inductive FacetKn2 (n : ℕ) : Type
  | base_diagonal (k : Fin n) : FacetKn2 n
  | chord (i j : Fin n) (hle : i.val ≤ j.val) : FacetKn2 n
  deriving DecidableEq

/-- The bijection mapping our combinatorial FacetKn2 directly to diagonals of the polygon. -/
def facetKn2_to_diagonal (n : ℕ) : FacetKn2 n → Diagonal n
  | FacetKn2.base_diagonal k => 
      have hk := k.isLt
      ⟨⟨0, by omega⟩, ⟨k.val + 2, by omega⟩, by dsimp; omega, by
        rintro ⟨h0, h2⟩
        dsimp at h0 h2
        omega⟩
  | FacetKn2.chord i j hle => 
      have hi := i.isLt
      have hj := j.isLt
      ⟨⟨i.val + 1, by omega⟩, ⟨j.val + 3, by omega⟩, by dsimp; omega, by
        rintro ⟨h0, h2⟩
        dsimp at h0 h2
        omega⟩

/-- The inverse mapping from geometric diagonals to combinatorial FacetKn2. -/
def diagonal_to_facetKn2 (n : ℕ) (d : Diagonal n) : FacetKn2 n :=
  if h0 : d.a.val = 0 then
    have hk : d.b.val - 2 < n := by
      have ha := d.ha
      have hb := d.b.isLt
      have hnb := d.h_not_base
      omega
    FacetKn2.base_diagonal ⟨d.b.val - 2, hk⟩
  else
    have hi : d.a.val - 1 < n := by
      have ha := d.ha
      have hb := d.b.isLt
      have ha_lt := d.a.isLt
      omega
    have hj : d.b.val - 3 < n := by
      have hb := d.b.isLt
      omega
    have hle : d.a.val - 1 ≤ d.b.val - 3 := by
      have ha := d.ha
      omega
    FacetKn2.chord ⟨d.a.val - 1, hi⟩ ⟨d.b.val - 3, hj⟩ hle

theorem facetKn2_diagonal_left_inv (n : ℕ) (f : FacetKn2 n) :
    diagonal_to_facetKn2 n (facetKn2_to_diagonal n f) = f := by
  cases f <;> (dsimp [facetKn2_to_diagonal, diagonal_to_facetKn2]; congr 1)

theorem facetKn2_diagonal_right_inv (n : ℕ) (d : Diagonal n) :
    facetKn2_to_diagonal n (diagonal_to_facetKn2 n d) = d := by
  dsimp [diagonal_to_facetKn2]
  split_ifs with h0
  · dsimp [facetKn2_to_diagonal]
    have ha := d.ha
    have hb := d.b.isLt
    apply Diagonal.ext
    · ext; dsimp; omega
    · ext; dsimp; omega
  · dsimp [facetKn2_to_diagonal]
    have ha := d.ha
    have hb := d.b.isLt
    have ha_lt := d.a.isLt
    apply Diagonal.ext
    · ext; dsimp; omega
    · ext; dsimp; omega

/-- Fully proven constructive equivalence between FacetKn2 and true polygon Diagonals. -/
def facetKn2_diagonal_equiv (n : ℕ) : FacetKn2 n ≃ Diagonal n where
  toFun := facetKn2_to_diagonal n
  invFun := diagonal_to_facetKn2 n
  left_inv := facetKn2_diagonal_left_inv n
  right_inv := facetKn2_diagonal_right_inv n

/-- Cyclic length of a chord in a convex (n+3)-gon. -/
def cyclicLength (n : ℕ) (d : Diagonal n) : ℕ :=
  min (d.b.val - d.a.val) ((n + 3) - (d.b.val - d.a.val))

def diagonalsOfLength (n l : ℕ) : Finset (Diagonal n) :=
  Finset.filter (fun d => cyclicLength n d = l) Finset.univ

def map_eq (n l : ℕ) (hl1 : 2 ≤ l) (hl3 : l * 2 = n + 3) (i : Fin ((n + 3) / 2)) : Diagonal n :=
  have h1 : i.val + 2 ≤ i.val + l := by omega
  have h2 : ¬(i.val = 0 ∧ i.val + l = n + 2) := by omega
  have ha : i.val < n + 3 := by omega
  have hb : i.val + l < n + 3 := by have := i.isLt; omega
  ⟨⟨i.val, ha⟩, ⟨i.val + l, hb⟩, h1, h2⟩

lemma map_eq_inj (n l : ℕ) (hl1 : 2 ≤ l) (hl3 : l * 2 = n + 3) :
    Function.Injective (map_eq n l hl1 hl3) := by
  intro i j hij
  have h_a : i.val = j.val := by
    have := congrArg (fun d => d.a.val) hij
    exact this
  exact Fin.ext h_a

lemma map_eq_mem (n l : ℕ) (hl1 : 2 ≤ l) (hl3 : l * 2 = n + 3) (i : Fin ((n + 3) / 2)) :
    map_eq n l hl1 hl3 i ∈ diagonalsOfLength n l := by
  dsimp [diagonalsOfLength]
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_univ
  · dsimp [cyclicLength, map_eq]
    have : i.val + l - i.val = l := by omega
    rw [this]
    have : n + 3 - l = l := by omega
    rw [this, min_self]

lemma map_eq_surj (n l : ℕ) (hl1 : 2 ≤ l) (hl3 : l * 2 = n + 3) (d : Diagonal n)
    (hd : d ∈ diagonalsOfLength n l) : ∃ i, map_eq n l hl1 hl3 i = d := by
  have hd2 : cyclicLength n d = l := by
    have : d ∈ Finset.filter (fun x => cyclicLength n x = l) Finset.univ := hd
    exact (Finset.mem_filter.mp this).2
  have h_min : min (d.b.val - d.a.val) (n + 3 - (d.b.val - d.a.val)) = l := hd2
  have h_len : d.b.val - d.a.val = l := by
    have h_min_eq := min_eq_iff.mp h_min
    cases h_min_eq with
    | inl h => exact h.1
    | inr h => omega
  have hia : d.a.val < (n + 3) / 2 := by
    have : d.b.val < n + 3 := d.b.isLt
    omega
  use ⟨d.a.val, hia⟩
  apply Diagonal.ext
  · apply Fin.ext
    exact rfl
  · apply Fin.ext
    change d.a.val + l = d.b.val
    omega

theorem cyclic_length_count_eq (n l : ℕ) (hl1 : 2 ≤ l) (hl3 : l * 2 = n + 3) :
    (diagonalsOfLength n l).card = (n + 3) / 2 := by
  have h_eq : diagonalsOfLength n l = Finset.image (map_eq n l hl1 hl3) Finset.univ := by
    ext d
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · exact map_eq_surj n l hl1 hl3 d
    · rintro ⟨i, hi⟩
      rw [← hi]
      exact map_eq_mem n l hl1 hl3 i
  rw [h_eq, Finset.card_image_of_injective Finset.univ (map_eq_inj n l hl1 hl3), Finset.card_univ, Fintype.card_fin]

def map_lt (n l : ℕ) (hl1 : 2 ≤ l) (hl3 : l * 2 < n + 3) (i : Fin (n + 3)) : Diagonal n :=
  if h_lt : i.val < n + 3 - l then
    have h1 : i.val + 2 ≤ i.val + l := by omega
    have h2 : ¬(i.val = 0 ∧ i.val + l = n + 2) := by omega
    have ha : i.val < n + 3 := by omega
    have hb : i.val + l < n + 3 := by omega
    ⟨⟨i.val, ha⟩, ⟨i.val + l, hb⟩, h1, h2⟩
  else
    have ha_val : i.val - (n + 3 - l) < n + 3 := by omega
    have hb_val : i.val - (n + 3 - l) + (n + 3 - l) < n + 3 := by omega
    have h1 : (i.val - (n + 3 - l)) + 2 ≤ (i.val - (n + 3 - l)) + (n + 3 - l) := by omega
    have h2 : ¬(i.val - (n + 3 - l) = 0 ∧ i.val - (n + 3 - l) + (n + 3 - l) = n + 2) := by omega
    ⟨⟨i.val - (n + 3 - l), ha_val⟩, ⟨i.val - (n + 3 - l) + (n + 3 - l), hb_val⟩, h1, h2⟩

lemma map_lt_inj (n l : ℕ) (hl1 : 2 ≤ l) (hl3 : l * 2 < n + 3) :
    Function.Injective (map_lt n l hl1 hl3) := by
  intro i j hij
  have h_a : (map_lt n l hl1 hl3 i).a.val = (map_lt n l hl1 hl3 j).a.val := congrArg (fun d => d.a.val) hij
  have h_b : (map_lt n l hl1 hl3 i).b.val = (map_lt n l hl1 hl3 j).b.val := congrArg (fun d => d.b.val) hij
  by_cases hi : i.val < n + 3 - l <;> by_cases hj : j.val < n + 3 - l
  · dsimp [map_lt] at h_a h_b
    rw [dif_pos hi, dif_pos hj] at h_a h_b
    exact Fin.ext h_a
  · dsimp [map_lt] at h_a h_b
    rw [dif_pos hi, dif_neg hj] at h_a h_b
    change i.val = j.val - (n + 3 - l) at h_a
    change i.val + l = j.val - (n + 3 - l) + (n + 3 - l) at h_b
    omega
  · dsimp [map_lt] at h_a h_b
    rw [dif_neg hi, dif_pos hj] at h_a h_b
    change i.val - (n + 3 - l) = j.val at h_a
    change i.val - (n + 3 - l) + (n + 3 - l) = j.val + l at h_b
    omega
  · dsimp [map_lt] at h_a h_b
    rw [dif_neg hi, dif_neg hj] at h_a h_b
    change i.val - (n + 3 - l) = j.val - (n + 3 - l) at h_a
    have : i.val = j.val := by omega
    exact Fin.ext this

lemma map_lt_mem (n l : ℕ) (hl1 : 2 ≤ l) (hl3 : l * 2 < n + 3) (i : Fin (n + 3)) :
    map_lt n l hl1 hl3 i ∈ diagonalsOfLength n l := by
  dsimp [diagonalsOfLength]
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_univ
  · dsimp [cyclicLength, map_lt]
    split_ifs with h_lt
    · have : i.val + l - i.val = l := by omega
      rw [this]
      apply min_eq_left
      omega
    · have : i.val - (n + 3 - l) + (n + 3 - l) - (i.val - (n + 3 - l)) = n + 3 - l := by omega
      rw [this]
      have : n + 3 - (n + 3 - l) = l := by omega
      rw [this]
      apply min_eq_right
      omega

lemma map_lt_surj (n l : ℕ) (hl1 : 2 ≤ l) (hl3 : l * 2 < n + 3) (d : Diagonal n)
    (hd : d ∈ diagonalsOfLength n l) : ∃ i, map_lt n l hl1 hl3 i = d := by
  have hd2 : cyclicLength n d = l := by
    have : d ∈ Finset.filter (fun x => cyclicLength n x = l) Finset.univ := hd
    exact (Finset.mem_filter.mp this).2
  have h_min : min (d.b.val - d.a.val) (n + 3 - (d.b.val - d.a.val)) = l := hd2
  cases min_eq_iff.mp h_min with
  | inl h => 
    have hl_eq : d.b.val - d.a.val = l := h.1
    have hia : d.a.val < n + 3 - l := by
      have : d.b.val < n + 3 := d.b.isLt
      omega
    use ⟨d.a.val, by omega⟩
    apply Diagonal.ext
    · apply Fin.ext
      dsimp [map_lt]
      rw [dif_pos hia]
    · apply Fin.ext
      dsimp [map_lt]
      rw [dif_pos hia]
      change d.a.val + l = d.b.val
      omega
  | inr h => 
    have hl_eq : n + 3 - (d.b.val - d.a.val) = l := h.1
    have h_diff : d.b.val - d.a.val = n + 3 - l := by omega
    have hia : d.a.val + (n + 3 - l) < n + 3 := by
      have : d.b.val < n + 3 := d.b.isLt
      omega
    use ⟨d.a.val + (n + 3 - l), hia⟩
    have h_not_lt : ¬(d.a.val + (n + 3 - l) < n + 3 - l) := by omega
    apply Diagonal.ext
    · apply Fin.ext
      dsimp [map_lt]
      rw [dif_neg h_not_lt]
      change (d.a.val + (n + 3 - l)) - (n + 3 - l) = d.a.val
      omega
    · apply Fin.ext
      dsimp [map_lt]
      rw [dif_neg h_not_lt]
      change (d.a.val + (n + 3 - l)) - (n + 3 - l) + (n + 3 - l) = d.b.val
      omega

theorem cyclic_length_count_lt (n l : ℕ) (hl1 : 2 ≤ l) (hl3 : l * 2 < n + 3) :
    (diagonalsOfLength n l).card = n + 3 := by
  have h_eq : diagonalsOfLength n l = Finset.image (map_lt n l hl1 hl3) Finset.univ := by
    ext d
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · exact map_lt_surj n l hl1 hl3 d
    · rintro ⟨i, hi⟩
      rw [← hi]
      exact map_lt_mem n l hl1 hl3 i
  rw [h_eq, Finset.card_image_of_injective Finset.univ (map_lt_inj n l hl1 hl3), Finset.card_univ, Fintype.card_fin]

/-- Diagonals of cyclic length ℓ number n+3, except when ℓ = (n+3)/2, where there are (n+3)/2. -/
theorem cyclic_length_count (n l : ℕ) (hl1 : 2 ≤ l) (hl2 : l ≤ (n + 3) / 2) :
    (diagonalsOfLength n l).card = if l * 2 = n + 3 then (n + 3) / 2 else n + 3 := by
  split_ifs with h
  · exact cyclic_length_count_eq n l hl1 h
  · have hl3 : l * 2 < n + 3 := by omega
    exact cyclic_length_count_lt n l hl1 hl3

/-- The 6/3 split for n=3 as a concrete instance. -/
theorem cyclic_length_count_3_2 : (diagonalsOfLength 3 2).card = 6 := by decide
theorem cyclic_length_count_3_3 : (diagonalsOfLength 3 3).card = 3 := by decide

/-- Canonical constructive bijection between Aₙ roots and K_{n+2} facets for all n. -/
def rootAn_to_facetKn2 (n : ℕ) : RootAn n → FacetKn2 n
  | RootAn.pos i j hle => FacetKn2.chord i j hle
  | RootAn.neg_simple k => FacetKn2.base_diagonal k

def facetKn2_to_rootAn (n : ℕ) : FacetKn2 n → RootAn n
  | FacetKn2.chord i j hle => RootAn.pos i j hle
  | FacetKn2.base_diagonal k => RootAn.neg_simple k

theorem rootAn_facet_left_inv (n : ℕ) (r : RootAn n) :
    facetKn2_to_rootAn n (rootAn_to_facetKn2 n r) = r := by
  cases r <;> rfl

theorem rootAn_facet_right_inv (n : ℕ) (f : FacetKn2 n) :
    rootAn_to_facetKn2 n (facetKn2_to_rootAn n f) = f := by
  cases f <;> rfl

/-- Universal Associahedron-Root Equivalence: RootAn n ≃ FacetKn2 n for all n : ℕ. -/
def rootAn_facetKn2_equiv (n : ℕ) : RootAn n ≃ FacetKn2 n where
  toFun := rootAn_to_facetKn2 n
  invFun := facetKn2_to_rootAn n
  left_inv := rootAn_facet_left_inv n
  right_inv := rootAn_facet_right_inv n

/-- Universal bijection between Aₙ roots and true polygon Diagonals. -/
def rootAn_diagonal_equiv (n : ℕ) : RootAn n ≃ Diagonal n :=
  (rootAn_facetKn2_equiv n).trans (facetKn2_diagonal_equiv n)

/-- Identify the root-indexing diagonal type with the general polygon face type. -/
def diagonal_polygon_equiv (n : ℕ) : Diagonal n ≃ PolygonDiagonal (n + 2) where
  toFun d := ⟨d.a, d.b, d.ha, d.h_not_base⟩
  invFun d := ⟨d.a, d.b, d.gap, d.not_boundary⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Almost-positive roots index actual supporting facets of the convex realization. -/
noncomputable def rootAn_lodayFacet_equiv (n : ℕ) :
    RootAn n ≃ {F : LodayExposedFace n // IsCoatom F} :=
  (rootAn_diagonal_equiv n).trans
    ((diagonal_polygon_equiv n).trans (polygonDiagonal_lodayFacet_equiv n))

/-! ### Support = Crossing in the Fan Model -/

/-- Two diagonals of the (n+3)-gon cross in their interiors. -/
def Diagonal.Crosses {n : ℕ} (d e : Diagonal n) : Prop :=
  (d.a.val < e.a.val ∧ e.a.val < d.b.val ∧ d.b.val < e.b.val) ∨
  (e.a.val < d.a.val ∧ d.a.val < e.b.val ∧ e.b.val < d.b.val)

instance {n : ℕ} (d e : Diagonal n) : Decidable (d.Crosses e) := by
  unfold Diagonal.Crosses; infer_instance

theorem Diagonal.crosses_comm {n : ℕ} (d e : Diagonal n) : d.Crosses e ↔ e.Crosses d := by
  unfold Diagonal.Crosses; omega

/-- The fan triangulation from vertex 0: diagonals (0, k+2). -/
def fanDiagonal (n : ℕ) (k : Fin n) : Diagonal n :=
  facetKn2_to_diagonal n (FacetKn2.base_diagonal k)

@[simp] theorem fanDiagonal_a (n : ℕ) (k : Fin n) : (fanDiagonal n k).a.val = 0 := rfl
@[simp] theorem fanDiagonal_b (n : ℕ) (k : Fin n) : (fanDiagonal n k).b.val = k.val + 2 := rfl

@[simp] theorem rootAn_diagonal_pos_a (n : ℕ) (i j : Fin n) (h : i.val ≤ j.val) :
    (rootAn_diagonal_equiv n (RootAn.pos i j h)).a.val = i.val + 1 := rfl
@[simp] theorem rootAn_diagonal_pos_b (n : ℕ) (i j : Fin n) (h : i.val ≤ j.val) :
    (rootAn_diagonal_equiv n (RootAn.pos i j h)).b.val = j.val + 3 := rfl

theorem rootAn_diagonal_neg_simple (n : ℕ) (k : Fin n) :
    rootAn_diagonal_equiv n (RootAn.neg_simple k) = fanDiagonal n k := rfl

/-- The fan diagonals are pairwise non-crossing (they form a triangulation). -/
theorem fanDiagonal_not_crosses (n : ℕ) (k l : Fin n) :
    ¬ (fanDiagonal n k).Crosses (fanDiagonal n l) := by
  simp only [Diagonal.Crosses, fanDiagonal_a]; omega

/-- **Support = crossing.** The diagonal of the positive root `α_{i..j}` crosses the
    fan diagonal `(0, k+2)` exactly when `k` lies in the support `[i, j]`. -/
theorem rootAn_pos_crosses_fan_iff (n : ℕ) (i j : Fin n) (hle : i.val ≤ j.val) (k : Fin n) :
    (rootAn_diagonal_equiv n (RootAn.pos i j hle)).Crosses (fanDiagonal n k) ↔
      i.val ≤ k.val ∧ k.val ≤ j.val := by
  simp only [Diagonal.Crosses, rootAn_diagonal_pos_a, rootAn_diagonal_pos_b,
    fanDiagonal_a, fanDiagonal_b]
  omega

/-- A diagonal crosses no fan diagonal iff it is itself a fan diagonal. -/
theorem crosses_no_fan_iff (n : ℕ) (d : Diagonal n) :
    (∀ k : Fin n, ¬ d.Crosses (fanDiagonal n k)) ↔ d.a.val = 0 := by
  have hab := d.ha
  have hb := d.b.isLt
  constructor
  · intro h
    by_contra ha
    apply h ⟨d.a.val - 1, by omega⟩
    simp only [Diagonal.Crosses, fanDiagonal_a, fanDiagonal_b]
    omega
  · intro ha k
    simp only [Diagonal.Crosses, fanDiagonal_a, fanDiagonal_b]
    omega

/-- The roots compatible with every element of the initial cluster (the fan) are exactly
    the negative simple roots. -/
theorem compatible_with_fan_iff_neg_simple (n : ℕ) (r : RootAn n) :
    (∀ k : Fin n, ¬ (rootAn_diagonal_equiv n r).Crosses (fanDiagonal n k)) ↔
      ∃ k, r = RootAn.neg_simple k := by
  rw [crosses_no_fan_iff]
  cases r with
  | pos i j h => simp
  | neg_simple k => exact ⟨fun _ => ⟨k, rfl⟩, fun _ => rfl⟩

/-! ### Explicit A₃ ≅ K₅ Dimension-3 Specialization -/

/-- The 9 almost-positive roots of A₃ (6 positive + 3 negative simple). -/
inductive RootA3 : Type
  | alpha1 : RootA3
  | alpha2 : RootA3
  | alpha3 : RootA3
  | alpha12 : RootA3
  | alpha23 : RootA3
  | alpha123 : RootA3
  | neg_alpha1 : RootA3
  | neg_alpha2 : RootA3
  | neg_alpha3 : RootA3
  deriving DecidableEq, Repr

open RootA3

/-- The 9 boundary facets of the 3D Associahedron K₅ (6 pentagons + 3 squares). -/
inductive FacetK5 : Type
  | pentagon (i : Fin 6) : FacetK5
  | square (j : Fin 3) : FacetK5
  deriving DecidableEq, Repr

def rootA3_to_facetKn2_3 : RootA3 → FacetKn2 3
  | neg_alpha1 => FacetKn2.base_diagonal ⟨0, by decide⟩
  | neg_alpha2 => FacetKn2.base_diagonal ⟨1, by decide⟩
  | neg_alpha3 => FacetKn2.base_diagonal ⟨2, by decide⟩
  | alpha1     => FacetKn2.chord ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide)
  | alpha2     => FacetKn2.chord ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide)
  | alpha3     => FacetKn2.chord ⟨2, by decide⟩ ⟨2, by decide⟩ (by decide)
  | alpha12    => FacetKn2.chord ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  | alpha23    => FacetKn2.chord ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
  | alpha123   => FacetKn2.chord ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)

def rootA3_to_rootAn3 : RootA3 → RootAn 3
  | neg_alpha1 => RootAn.neg_simple ⟨0, by decide⟩
  | neg_alpha2 => RootAn.neg_simple ⟨1, by decide⟩
  | neg_alpha3 => RootAn.neg_simple ⟨2, by decide⟩
  | alpha1     => RootAn.pos ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide)
  | alpha2     => RootAn.pos ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide)
  | alpha3     => RootAn.pos ⟨2, by decide⟩ ⟨2, by decide⟩ (by decide)
  | alpha12    => RootAn.pos ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  | alpha23    => RootAn.pos ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
  | alpha123   => RootAn.pos ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)

theorem rootA3_to_facetKn2_3_eq (r : RootA3) :
    rootA3_to_facetKn2_3 r = rootAn_to_facetKn2 3 (rootA3_to_rootAn3 r) := by
  cases r <;> rfl

def rootAn3_to_rootA3 (r : RootAn 3) : RootA3 :=
  if r = RootAn.neg_simple ⟨0, by decide⟩ then neg_alpha1
  else if r = RootAn.neg_simple ⟨1, by decide⟩ then neg_alpha2
  else if r = RootAn.neg_simple ⟨2, by decide⟩ then neg_alpha3
  else if r = RootAn.pos ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide) then alpha1
  else if r = RootAn.pos ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) then alpha2
  else if r = RootAn.pos ⟨2, by decide⟩ ⟨2, by decide⟩ (by decide) then alpha3
  else if r = RootAn.pos ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) then alpha12
  else if r = RootAn.pos ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) then alpha23
  else if r = RootAn.pos ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) then alpha123
  else neg_alpha1

def rootA3_equiv_rootAn3 : RootA3 ≃ RootAn 3 where
  toFun := rootA3_to_rootAn3
  invFun := rootAn3_to_rootA3
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨i, hi⟩, ⟨j, hj⟩, hle⟩ | ⟨⟨k, hk⟩⟩
    · interval_cases i <;> interval_cases j <;> try rfl
    · interval_cases k <;> rfl

def rootA3_to_diagonal_3 (r : RootA3) : Diagonal 3 :=
  facetKn2_to_diagonal 3 (rootA3_to_facetKn2_3 r)

def rootA3_cyclic_length (r : RootA3) : ℕ :=
  cyclicLength 3 (rootA3_to_diagonal_3 r)

/-- Classification reflecting cyclic diagonal lengths in the hexagon (n=3+3=6). 
    - Pentagons (cyclic length 2 diagonals): (0,2), (1,3), (2,4), (3,5), (0,4), (1,5).
    - Squares (cyclic length 3 diagonals): (0,3), (1,4), (2,5). -/
def rootA3_to_facetK5 (r : RootA3) : FacetK5 :=
  match r with
  | neg_alpha1 => FacetK5.pentagon 0
  | neg_alpha2 => FacetK5.square 0
  | neg_alpha3 => FacetK5.pentagon 1
  | alpha1     => FacetK5.pentagon 2
  | alpha12    => FacetK5.square 1
  | alpha123   => FacetK5.pentagon 3
  | alpha2     => FacetK5.pentagon 4
  | alpha23    => FacetK5.square 2
  | alpha3     => FacetK5.pentagon 5

def facetK5_to_rootA3 (f : FacetK5) : RootA3 :=
  match f with
  | FacetK5.pentagon 0 => neg_alpha1
  | FacetK5.square 0   => neg_alpha2
  | FacetK5.pentagon 1 => neg_alpha3
  | FacetK5.pentagon 2 => alpha1
  | FacetK5.square 1   => alpha12
  | FacetK5.pentagon 3 => alpha123
  | FacetK5.pentagon 4 => alpha2
  | FacetK5.square 2   => alpha23
  | FacetK5.pentagon 5 => alpha3

theorem rootA3_facet_left_inv (r : RootA3) :
    facetK5_to_rootA3 (rootA3_to_facetK5 r) = r := by
  cases r <;> rfl

theorem rootA3_facet_right_inv (f : FacetK5) :
    rootA3_to_facetK5 (facetK5_to_rootA3 f) = f := by
  cases f with
  | pentagon i => rcases i with ⟨v, hv⟩; interval_cases v <;> rfl
  | square j => rcases j with ⟨v, hv⟩; interval_cases v <;> rfl

def rootA3_facetK5_equiv_direct : RootA3 ≃ FacetK5 where
  toFun := rootA3_to_facetK5
  invFun := facetK5_to_rootA3
  left_inv := rootA3_facet_left_inv
  right_inv := rootA3_facet_right_inv

def diagonal3_facetK5_equiv : Diagonal 3 ≃ FacetK5 :=
  (rootAn_diagonal_equiv 3).symm.trans (rootA3_equiv_rootAn3.symm.trans rootA3_facetK5_equiv_direct)

/-- The A₃ root system is in honest constructive bijection with the 9 facets of K₅, 
    matching diagonal lengths correctly. Routed through the general Diagonal n map. -/
def rootA3_facetK5_equiv : RootA3 ≃ FacetK5 :=
  rootA3_equiv_rootAn3.trans ((rootAn_diagonal_equiv 3).trans diagonal3_facetK5_equiv)

theorem rootA3_cyclic_length_pentagon (r : RootA3) (i : Fin 6) (h : rootA3_facetK5_equiv r = FacetK5.pentagon i) :
    rootA3_cyclic_length r = 2 := by
  have heq : rootA3_facetK5_equiv r = rootA3_to_facetK5 r := by cases r <;> rfl
  rw [heq] at h
  cases r <;> (first | rfl | cases h)

theorem rootA3_cyclic_length_square (r : RootA3) (j : Fin 3) (h : rootA3_facetK5_equiv r = FacetK5.square j) :
    rootA3_cyclic_length r = 3 := by
  have heq : rootA3_facetK5_equiv r = rootA3_to_facetK5 r := by cases r <;> rfl
  rw [heq] at h
  cases r <;> (first | rfl | cases h)

/-- The legacy A₃ cyclic-length labels agree with the general geometric index. -/
theorem rootA3_polygon_cyclic_length (r : RootA3) :
    polygonCyclicLength (diagonal_polygon_equiv 3 (rootA3_to_diagonal_3 r)) =
      rootA3_cyclic_length r := by
  cases r <;> rfl

/-- A pentagon label identifies an actual facet with the pentagon face order. -/
theorem rootA3_geometric_pentagonal_facet (r : RootA3) (i : Fin 6)
    (h : rootA3_facetK5_equiv r = FacetK5.pentagon i) :
    Nonempty (LodayFacetFaces 3 (diagonal_polygon_equiv 3 (rootA3_to_diagonal_3 r)) ≃o
      LodayExposedFace 2) :=
  Loday_K5_pentagonal_facet _ ((rootA3_polygon_cyclic_length r).trans
    (rootA3_cyclic_length_pentagon r i h))

/-- A square label identifies an actual facet with the product of two interval face orders. -/
theorem rootA3_geometric_square_facet (r : RootA3) (j : Fin 3)
    (h : rootA3_facetK5_equiv r = FacetK5.square j) :
    Nonempty (LodayFacetFaces 3 (diagonal_polygon_equiv 3 (rootA3_to_diagonal_3 r)) ≃o
      (LodayExposedFace 1 × LodayExposedFace 1)) :=
  Loday_K5_square_facet _ ((rootA3_polygon_cyclic_length r).trans
    (rootA3_cyclic_length_square r j h))

instance : Fintype RootA3 where
  elems := {alpha1, alpha2, alpha3, alpha12, alpha23, alpha123, neg_alpha1, neg_alpha2, neg_alpha3}
  complete := by intro x; cases x <;> simp

/-- The root / facet count is exactly 9. -/
theorem a3_facet_count : Fintype.card RootA3 = 9 := rfl

end AssociahedraDuality

/-! ==============================================================================
    SECTION 5: THE Aₙ CARTAN METRIC AND QUADRATIC FORM
    ============================================================================== -/

section CartanMetric

open BigOperators

/-! ### Universal N-Dimensional Aₙ Dirichlet-Cartan Energy -/

/-- Extended vector with Dirichlet boundary conditions: v(0) = 0 and v(i) = 0 for i > n. -/
def extVec (n : ℕ) (v : Fin n → ℤ) (i : ℕ) : ℤ :=
  if h : 0 < i ∧ i ≤ n then v ⟨i - 1, by omega⟩ else 0

@[simp] theorem extVec_zero (n : ℕ) (v : Fin n → ℤ) : extVec n v 0 = 0 := by
  dsimp [extVec]

theorem extVec_val (n : ℕ) (v : Fin n → ℤ) (k : Fin n) :
    extVec n v (k.val + 1) = v k := by
  dsimp [extVec]
  have h : 0 < k.val + 1 ∧ k.val + 1 ≤ n := by omega
  simp [h]

/-- The General Aₙ Cartan Quadratic Form as a discrete Dirichlet energy on ℤⁿ. -/
def cartanEnergy (n : ℕ) (v : Fin n → ℤ) : ℤ :=
  ∑ i : Fin (n + 1), (extVec n v (i.val + 1) - extVec n v i.val)^2

/-- Universal positive semi-definiteness of the Aₙ Cartan form for all n. -/
theorem cartanEnergy_nonneg (n : ℕ) (v : Fin n → ℤ) : 0 ≤ cartanEnergy n v := by
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg _

/-- Universal positive definiteness of the Aₙ Cartan form for all n. -/
theorem cartanEnergy_pos_def (n : ℕ) (v : Fin n → ℤ) :
    cartanEnergy n v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hterms : ∀ i : Fin (n + 1),
        (extVec n v (i.val + 1) - extVec n v i.val)^2 = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp h i (Finset.mem_univ i)
    have hdiff : ∀ i : ℕ, i ≤ n → extVec n v (i + 1) = extVec n v i := by
      intro i hi
      have sqz := hterms ⟨i, by omega⟩
      have sq0 : extVec n v (i + 1) - extVec n v i = 0 := sq_eq_zero_iff.mp sqz
      exact sub_eq_zero.mp sq0
    have hext_zero : ∀ m : ℕ, m ≤ n + 1 → extVec n v m = 0 := by
      intro m hm
      induction m with
      | zero => exact extVec_zero n v
      | succ m ih =>
        rw [hdiff m (by omega), ih (by omega)]
    funext k
    have hval := extVec_val n v k
    have hz := hext_zero (k.val + 1) (by omega)
    rw [← hval, hz]
    rfl
  · rintro rfl
    dsimp [cartanEnergy, extVec]
    have h_zero : ∀ i : Fin (n + 1),
        ((if 0 < i.val + 1 ∧ i.val + 1 ≤ n then (0 : ℤ) else 0) -
         (if 0 < i.val ∧ i.val ≤ n then (0 : ℤ) else 0))^2 = 0 := by
      intro i
      split_ifs <;> simp
    have hsum : (∑ i : Fin (n + 1),
        ((if 0 < i.val + 1 ∧ i.val + 1 ≤ n then (0 : ℤ) else 0) -
         (if 0 < i.val ∧ i.val ≤ n then (0 : ℤ) else 0))^2) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      exact h_zero x
    exact hsum

/-! ### Explicit A₃ Vector Space Specialization -/

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
end Vec3

open Vec3

/-- The A₃ Cartan Bilinear Form on ℤ³. -/
def cartanForm (u v : Vec3) : ℤ :=
  2 * u.x * v.x + 2 * u.y * v.y + 2 * u.z * v.z -
  (u.x * v.y + u.y * v.x) - (u.y * v.z + u.z * v.y)

theorem cartanForm_symm (u v : Vec3) : cartanForm u v = cartanForm v u := by
  dsimp [cartanForm]; ring

/-- Exact sum-of-squares decomposition of the A₃ quadratic form. -/
theorem cartanForm_sum_of_squares (v : Vec3) :
    cartanForm v v = v.x^2 + (v.x - v.y)^2 + (v.y - v.z)^2 + v.z^2 := by
  dsimp [cartanForm]; ring

theorem cartanForm_nonneg (v : Vec3) : 0 ≤ cartanForm v v := by
  rw [cartanForm_sum_of_squares]
  have h1 : 0 ≤ v.x^2 := sq_nonneg v.x
  have h2 : 0 ≤ (v.x - v.y)^2 := sq_nonneg (v.x - v.y)
  have h3 : 0 ≤ (v.y - v.z)^2 := sq_nonneg (v.y - v.z)
  have h4 : 0 ≤ v.z^2 := sq_nonneg v.z
  linarith

theorem cartanForm_pos_def (v : Vec3) : cartanForm v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [cartanForm_sum_of_squares] at h
    have hx0 : v.x = 0 := by nlinarith [sq_nonneg v.x, sq_nonneg (v.x - v.y), sq_nonneg (v.y - v.z), sq_nonneg v.z]
    have hz0 : v.z = 0 := by nlinarith [sq_nonneg v.x, sq_nonneg (v.x - v.y), sq_nonneg (v.y - v.z), sq_nonneg v.z]
    have hy0 : v.y = 0 := by nlinarith [sq_nonneg v.x, sq_nonneg (v.x - v.y), sq_nonneg (v.y - v.z), sq_nonneg v.z]
    ext <;> assumption
  · rintro rfl; rfl

def alpha1 : Vec3 := ⟨1, 0, 0⟩
def alpha2 : Vec3 := ⟨0, 1, 0⟩
def alpha3 : Vec3 := ⟨0, 0, 1⟩
def alpha12 : Vec3 := ⟨1, 1, 0⟩
def alpha23 : Vec3 := ⟨0, 1, 1⟩
def alpha123 : Vec3 := ⟨1, 1, 1⟩

theorem norm_alpha1 : cartanForm alpha1 alpha1 = 2 := by rfl
theorem norm_alpha2 : cartanForm alpha2 alpha2 = 2 := by rfl
theorem norm_alpha3 : cartanForm alpha3 alpha3 = 2 := by rfl
theorem norm_alpha12 : cartanForm alpha12 alpha12 = 2 := by rfl
theorem norm_alpha23 : cartanForm alpha23 alpha23 = 2 := by rfl
theorem norm_alpha123 : cartanForm alpha123 alpha123 = 2 := by rfl

theorem strain_adjacent_12 : cartanForm alpha1 alpha2 = -1 := by rfl
theorem strain_adjacent_23 : cartanForm alpha2 alpha3 = -1 := by rfl
theorem strain_orthogonal_13 : cartanForm alpha1 alpha3 = 0 := by rfl

theorem coupled_strain_alpha12 :
    cartanForm alpha12 alpha12 =
      cartanForm alpha1 alpha1 +
      cartanForm alpha2 alpha2 +
      2 * cartanForm alpha1 alpha2 := rfl

/-- Embedding of RootA3 into the ℤ³ root space Vec3. -/
def rootA3_to_vec3 : RootA3 → Vec3
  | RootA3.alpha1     => alpha1
  | RootA3.alpha2     => alpha2
  | RootA3.alpha3     => alpha3
  | RootA3.alpha12    => alpha12
  | RootA3.alpha23    => alpha23
  | RootA3.alpha123   => alpha123
  | RootA3.neg_alpha1 => ⟨-1, 0, 0⟩
  | RootA3.neg_alpha2 => ⟨0, -1, 0⟩
  | RootA3.neg_alpha3 => ⟨0, 0, -1⟩

/-- A vector in ℤ³ is a root of A₃ iff its Cartan norm is exactly 2. -/
def IsRootA3 (v : Vec3) : Prop :=
  cartanForm v v = 2

/-- An almost-positive root is a root that is either non-negative in all coordinates
    or is a negative simple root. -/
def IsAlmostPositiveRootA3 (v : Vec3) : Prop :=
  IsRootA3 v ∧
  ((0 ≤ v.x ∧ 0 ≤ v.y ∧ 0 ≤ v.z) ∨
   (v = ⟨-1, 0, 0⟩ ∨ v = ⟨0, -1, 0⟩ ∨ v = ⟨0, 0, -1⟩))

/-- Coordinate bounds derived from the sum-of-squares Cartan energy. -/
theorem root_bounds (v : Vec3) (h : IsRootA3 v) :
    -1 ≤ v.x ∧ v.x ≤ 1 ∧
    -2 ≤ v.y ∧ v.y ≤ 2 ∧
    -1 ≤ v.z ∧ v.z ≤ 1 := by
  have hsq : v.x ^ 2 + (v.x - v.y) ^ 2 + (v.y - v.z) ^ 2 + v.z ^ 2 = 2 := by
    rw [← cartanForm_sum_of_squares]
    exact h
  have hx : v.x ^ 2 ≤ 2 := by nlinarith [sq_nonneg (v.x - v.y), sq_nonneg (v.y - v.z), sq_nonneg v.z]
  have hz : v.z ^ 2 ≤ 2 := by nlinarith [sq_nonneg v.x, sq_nonneg (v.x - v.y), sq_nonneg (v.y - v.z)]
  have hxy : (v.x - v.y) ^ 2 ≤ 2 := by nlinarith [sq_nonneg v.x, sq_nonneg (v.y - v.z), sq_nonneg v.z]
  have hyz : (v.y - v.z) ^ 2 ≤ 2 := by nlinarith [sq_nonneg v.x, sq_nonneg (v.x - v.y), sq_nonneg v.z]
  have hx_bd : -1 ≤ v.x ∧ v.x ≤ 1 := by
    constructor
    · by_contra hc
      have : v.x ≤ -2 := by omega
      nlinarith [hx]
    · by_contra hc
      have : v.x ≥ 2 := by omega
      nlinarith [hx]
  have hz_bd : -1 ≤ v.z ∧ v.z ≤ 1 := by
    constructor
    · by_contra hc
      have : v.z ≤ -2 := by omega
      nlinarith [hz]
    · by_contra hc
      have : v.z ≥ 2 := by omega
      nlinarith [hz]
  have hy_bd : -2 ≤ v.y ∧ v.y ≤ 2 := by
    constructor
    · by_contra hc
      have : v.y ≤ -3 := by omega
      have hx1 : -1 ≤ v.x := hx_bd.1
      have : (v.x - v.y) ≥ 2 := by omega
      nlinarith [hxy]
    · by_contra hc
      have : v.y ≥ 3 := by omega
      have hx2 : v.x ≤ 1 := hx_bd.2
      have : (v.x - v.y) ≤ -2 := by omega
      nlinarith [hxy]
  exact ⟨hx_bd.1, hx_bd.2, hy_bd.1, hy_bd.2, hz_bd.1, hz_bd.2⟩

/-- The root embedding rootA3_to_vec3 is injective. -/
theorem rootA3_to_vec3_injective : Function.Injective rootA3_to_vec3 := by
  intro a b h
  cases a <;> cases b <;> first | rfl | revert h; decide

/-- The 9 constructors of RootA3 precisely classify the almost-positive roots of A₃. -/
theorem isAlmostPositiveRootA3_iff (v : Vec3) :
    IsAlmostPositiveRootA3 v ↔ ∃ r : RootA3, rootA3_to_vec3 r = v := by
  constructor
  · rintro ⟨hroot, hpos | hneg⟩
    · by_cases h1 : v = alpha1
      · exact ⟨RootA3.alpha1, h1 ▸ rfl⟩
      · by_cases h2 : v = alpha2
        · exact ⟨RootA3.alpha2, h2 ▸ rfl⟩
        · by_cases h3 : v = alpha3
          · exact ⟨RootA3.alpha3, h3 ▸ rfl⟩
          · by_cases h12 : v = alpha12
            · exact ⟨RootA3.alpha12, h12 ▸ rfl⟩
            · by_cases h23 : v = alpha23
              · exact ⟨RootA3.alpha23, h23 ▸ rfl⟩
              · by_cases h123 : v = alpha123
                · exact ⟨RootA3.alpha123, h123 ▸ rfl⟩
                · exfalso
                  have hbd := root_bounds v hroot
                  have hnorm : v.x ^ 2 + (v.x - v.y) ^ 2 + (v.y - v.z) ^ 2 + v.z ^ 2 = 2 := by
                    rw [← cartanForm_sum_of_squares]; exact hroot
                  rcases v with ⟨vx, vy, vz⟩
                  dsimp at hbd hpos
                  rcases hbd with ⟨hx1, hx2, hy1, hy2, hz1, hz2⟩
                  have hx_cases : vx = 0 ∨ vx = 1 := by omega
                  have hy_cases : vy = 0 ∨ vy = 1 ∨ vy = 2 := by omega
                  have hz_cases : vz = 0 ∨ vz = 1 := by omega
                  dsimp [alpha1, alpha2, alpha3, alpha12, alpha23, alpha123] at h1 h2 h3 h12 h23 h123 hnorm
                  rcases hx_cases with rx | rx <;> rcases hy_cases with ry | ry | ry <;> rcases hz_cases with rz | rz
                  · rw [rx, ry, rz] at hnorm; revert hnorm; decide
                  · subst rx ry rz; exact h3 rfl
                  · subst rx ry rz; exact h2 rfl
                  · subst rx ry rz; exact h23 rfl
                  · rw [rx, ry, rz] at hnorm; revert hnorm; decide
                  · rw [rx, ry, rz] at hnorm; revert hnorm; decide
                  · subst rx ry rz; exact h1 rfl
                  · rw [rx, ry, rz] at hnorm; revert hnorm; decide
                  · subst rx ry rz; exact h12 rfl
                  · subst rx ry rz; exact h123 rfl
                  · rw [rx, ry, rz] at hnorm; revert hnorm; decide
                  · rw [rx, ry, rz] at hnorm; revert hnorm; decide
    · rcases hneg with rfl | rfl | rfl
      · exact ⟨RootA3.neg_alpha1, rfl⟩
      · exact ⟨RootA3.neg_alpha2, rfl⟩
      · exact ⟨RootA3.neg_alpha3, rfl⟩
  · rintro ⟨r, rfl⟩
    constructor
    · cases r <;> rfl
    · cases r <;> {
        first
        | left; refine ⟨by decide, by decide, by decide⟩
        | right; first | left; rfl | right; first | left; rfl | right; rfl
      }

/-- Every almost-positive A₃ root has squared norm exactly 2 under the Cartan metric. -/
theorem rootA3_cartan_norm (r : RootA3) :
    cartanForm (rootA3_to_vec3 r) (rootA3_to_vec3 r) = 2 := by
  cases r <;> rfl


open Finset

/-! ### The Dirichlet Energy is the Aₙ Cartan Matrix Form -/

/-- The Aₙ Cartan matrix: 2 on the diagonal, −1 on the first off-diagonals. -/
def cartanMatrix (n : ℕ) (i j : Fin n) : ℤ :=
  if i.val = j.val then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

theorem cartanEnergy_eq_range (n : ℕ) (v : Fin n → ℤ) :
    cartanEnergy n v = ∑ t ∈ range (n + 1), (extVec n v (t + 1) - extVec n v t) ^ 2 :=
  Fin.sum_univ_eq_sum_range (fun t => (extVec n v (t + 1) - extVec n v t) ^ 2) (n + 1)

theorem extVec_of_lt (n : ℕ) (v : Fin n → ℤ) (t : ℕ) (ht : n < t) : extVec n v t = 0 := by
  unfold extVec; rw [dif_neg (by omega)]

theorem extVec_of_pos (n : ℕ) (v : Fin n → ℤ) (t : ℕ) (h0 : 0 < t) (hn : t ≤ n) :
    extVec n v t = v ⟨t - 1, by omega⟩ := by
  unfold extVec; rw [dif_pos ⟨h0, hn⟩]

/-- Discrete summation by parts (Green's identity) for sequences vanishing at 0. -/
theorem sum_sq_diff_telescope (w : ℕ → ℤ) (h0 : w 0 = 0) (N : ℕ) :
    ∑ t ∈ range N, (w (t + 1) - w t) ^ 2 =
      ∑ t ∈ range N, w (t + 1) * (2 * w (t + 1) - w t - w (t + 2)) +
        w N * (w (N + 1) - w N) := by
  induction N with
  | zero => simp [h0]
  | succ N ih => rw [sum_range_succ, sum_range_succ, ih]; ring

theorem range_sum_eq_fin_sum (F : ℕ → ℤ) (n : ℕ) :
    ∑ t ∈ range n, F t = ∑ i : Fin n, F i.val :=
  (Fin.sum_univ_eq_sum_range F n).symm

/-- Row `i` of `C v`: `(C v)_i = 2 v_i − v_{i−1} − v_{i+1}` with zero boundary values. -/
theorem cartanMatrix_row (n : ℕ) (v : Fin n → ℤ) (i : Fin n) :
    ∑ j, cartanMatrix n i j * v j =
      2 * v i - extVec n v i.val - extVec n v (i.val + 2) := by
  have hi := i.isLt
  have split : ∀ j : Fin n, cartanMatrix n i j * v j =
      (if j.val = i.val then 2 * v j else 0) +
      (if j.val + 1 = i.val then -v j else 0) +
      (if i.val + 1 = j.val then -v j else 0) := by
    intro j; unfold cartanMatrix; split_ifs <;> omega
  simp only [split, sum_add_distrib]
  have s1 : ∑ j : Fin n, (if j.val = i.val then 2 * v j else 0) = 2 * v i := by
    rw [Fintype.sum_eq_single i (fun j hj => if_neg (fun h => hj (Fin.ext h)))]
    simp
  have s2 : ∑ j : Fin n, (if j.val + 1 = i.val then -v j else 0) = -extVec n v i.val := by
    by_cases h0 : i.val = 0
    · rw [h0, extVec_zero]
      exact Finset.sum_eq_zero (fun j _ => if_neg (by omega))
    · rw [extVec_of_pos n v i.val (by omega) (by omega),
        Fintype.sum_eq_single ⟨i.val - 1, by omega⟩ (fun j hj => if_neg (fun h =>
          hj (Fin.ext (by simp only; omega))))]
      simp only
      rw [if_pos (by omega)]
  have s3 : ∑ j : Fin n, (if i.val + 1 = j.val then -v j else 0) =
      -extVec n v (i.val + 2) := by
    by_cases hn : i.val + 1 < n
    · rw [extVec_of_pos n v (i.val + 2) (by omega) (by omega),
        Fintype.sum_eq_single ⟨i.val + 1, hn⟩ (fun j hj => if_neg (fun h =>
          hj (Fin.ext (by simp only; omega))))]
      simp only [if_true]
      rfl
    · rw [extVec_of_lt n v (i.val + 2) (by omega)]
      simp only [neg_zero]
      exact Finset.sum_eq_zero (fun j _ => if_neg (by have := j.isLt; omega))
  rw [s1, s2, s3]; ring

/-- **The Dirichlet energy is the Cartan form:** `cartanEnergy n v = vᵀ C_{Aₙ} v`. -/
theorem cartanEnergy_eq_cartanMatrix (n : ℕ) (v : Fin n → ℤ) :
    cartanEnergy n v = ∑ i, ∑ j, cartanMatrix n i j * v i * v j := by
  have rhs : ∀ i : Fin n, ∑ j, cartanMatrix n i j * v i * v j =
      v i * (2 * v i - extVec n v i.val - extVec n v (i.val + 2)) := by
    intro i
    rw [← cartanMatrix_row, Finset.mul_sum]
    exact sum_congr rfl (fun j _ => by ring)
  rw [sum_congr rfl (fun i _ => rhs i), cartanEnergy_eq_range,
    sum_sq_diff_telescope _ (extVec_zero n v), extVec_of_lt n v (n + 1) (by omega),
    zero_mul, add_zero, sum_range_succ, extVec_of_lt n v (n + 1) (by omega), zero_mul,
    add_zero, range_sum_eq_fin_sum]
  exact sum_congr rfl (fun i _ => by rw [extVec_val])

/-- For n = 3 the Dirichlet energy agrees with the explicit form `cartanForm` on `Vec3`. -/
theorem cartanEnergy_three (v : Fin 3 → ℤ) :
    cartanEnergy 3 v = cartanForm ⟨v 0, v 1, v 2⟩ ⟨v 0, v 1, v 2⟩ := by
  rw [cartanEnergy_eq_range]
  simp only [sum_range_succ, sum_range_zero, extVec, cartanForm]
  norm_num
  rw [show (⟨2, by omega⟩ : Fin 3) = 2 from rfl]
  ring

/-! ### Root Vectors and Norm 2 for Every n -/

/-- Simple-root coordinates of an almost-positive root: `α_{i..j} ↦ 𝟙_{[i,j]}`, `−α_k ↦ −e_k`. -/
def rootAn_to_vec (n : ℕ) : RootAn n → Fin n → ℤ
  | RootAn.pos i j _ => fun m => if i.val ≤ m.val ∧ m.val ≤ j.val then 1 else 0
  | RootAn.neg_simple k => fun m => if m.val = k.val then -1 else 0

theorem extVec_rootAn_pos (n : ℕ) (i j : Fin n) (h : i.val ≤ j.val) (t : ℕ) :
    extVec n (rootAn_to_vec n (RootAn.pos i j h)) t =
      if i.val + 1 ≤ t ∧ t ≤ j.val + 1 then 1 else 0 := by
  have := j.isLt
  unfold extVec rootAn_to_vec
  split_ifs <;> (try simp only at *) <;> omega

theorem extVec_rootAn_neg (n : ℕ) (k : Fin n) (t : ℕ) :
    extVec n (rootAn_to_vec n (RootAn.neg_simple k)) t =
      if t = k.val + 1 then -1 else 0 := by
  have := k.isLt
  unfold extVec rootAn_to_vec
  split_ifs <;> (try simp only at *) <;> omega

/-- **Norm 2 for all n:** every almost-positive root of Aₙ has Cartan energy exactly 2. -/
theorem rootAn_cartan_norm (n : ℕ) (r : RootAn n) :
    cartanEnergy n (rootAn_to_vec n r) = 2 := by
  rw [cartanEnergy_eq_range]
  cases r with
  | pos i j h =>
    have hj := j.isLt
    have term : ∀ t ∈ range (n + 1),
        (extVec n (rootAn_to_vec n (RootAn.pos i j h)) (t + 1) -
          extVec n (rootAn_to_vec n (RootAn.pos i j h)) t) ^ 2 =
        (if t = i.val then 1 else 0) + (if t = j.val + 1 then 1 else 0) := by
      intro t _
      rw [extVec_rootAn_pos, extVec_rootAn_pos]
      split_ifs <;> (try norm_num) <;> omega
    rw [sum_congr rfl term, sum_add_distrib, sum_ite_eq', sum_ite_eq',
      if_pos (mem_range.mpr (by omega)), if_pos (mem_range.mpr (by omega))]
    norm_num
  | neg_simple k =>
    have hk := k.isLt
    have term : ∀ t ∈ range (n + 1),
        (extVec n (rootAn_to_vec n (RootAn.neg_simple k)) (t + 1) -
          extVec n (rootAn_to_vec n (RootAn.neg_simple k)) t) ^ 2 =
        (if t = k.val then 1 else 0) + (if t = k.val + 1 then 1 else 0) := by
      intro t _
      rw [extVec_rootAn_neg, extVec_rootAn_neg]
      split_ifs <;> (try norm_num) <;> omega
    rw [sum_congr rfl term, sum_add_distrib, sum_ite_eq', sum_ite_eq',
      if_pos (mem_range.mpr (by omega)), if_pos (mem_range.mpr (by omega))]
    norm_num

/-- Distinct almost-positive roots have distinct coordinate vectors. -/
theorem rootAn_to_vec_injective (n : ℕ) : Function.Injective (rootAn_to_vec n) := by
  intro r s hrs
  cases r with
  | pos i j hij =>
    cases s with
    | pos i' j' hij' =>
      have h1 := congrFun hrs i
      have h2 := congrFun hrs i'
      have h3 := congrFun hrs j
      have h4 := congrFun hrs j'
      simp only [rootAn_to_vec] at h1 h2 h3 h4
      have hi : i = i' := Fin.ext (by split_ifs at h1 h2 h3 h4 <;> omega)
      have hj : j = j' := Fin.ext (by split_ifs at h1 h2 h3 h4 <;> omega)
      subst hi hj; rfl
    | neg_simple k =>
      have h1 := congrFun hrs i
      simp only [rootAn_to_vec] at h1
      split_ifs at h1 <;> omega
  | neg_simple k =>
    cases s with
    | pos i' j' hij' =>
      have h1 := congrFun hrs i'
      simp only [rootAn_to_vec] at h1
      split_ifs at h1 <;> omega
    | neg_simple k' =>
      have h1 := congrFun hrs k
      simp only [rootAn_to_vec] at h1
      have hk : k = k' := Fin.ext (by split_ifs at h1 <;> omega)
      subst hk; rfl

end CartanMetric


end FunctorialGeometry
#print axioms FunctorialGeometry.cyclic_length_count
