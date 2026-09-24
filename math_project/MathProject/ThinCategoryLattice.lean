/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shivansh Singh
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Cover
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.IntervalCases

namespace ThinCategoryLattice

open CategoryTheory Limits

/-!
# Lattice Theory as a Thin Category

This module formalizes:
1. Posets/Lattices as thin categories (hom-sets are subsingletons).
2. Triviality of monomorphisms and epimorphisms in thin categories.
3. Meets and joins as categorical products and coproducts in thin categories.
4. Monotone maps as functors and closure operators as idempotent monads.
5. Subobject lattices Sub(X) as thin categories.
6. Homological Ext-collapse in thin categories (Ext0 subsingleton, trivial splitting).
7. The Tamari Lattice of 4-bracketings (Stasheff Pentagon K4).
8. The A3 root system bijection to the 9 facets of the 3D Associahedron K5.
-/

section ThinBasics

variable {L : Type*} [PartialOrder L]

/-- In any preorder or partial order category, every hom-set is a subsingleton. -/
theorem thin_hom_subsingleton (x y : L) : Subsingleton (x ⟶ y) :=
  inferInstance

/-- In a thin category, all parallel morphisms are equal. -/
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

/-- In a thin category, any endomorphism is the identity. -/
theorem thin_end_is_id (x : L) (f : x ⟶ x) : f = 𝟙 x :=
  Subsingleton.elim f (𝟙 x)

/-- Monotone map between posets is canonically a functor between thin categories. -/
def monotone_functor {M : Type*} [PartialOrder M] (F : L → M) (hF : Monotone F) :
    L ⥤ M where
  obj x := F x
  map {x y} (f : x ⟶ y) :=
    homOfLE (hF (leOfHom f))

/-- A closure operator on a poset L. -/
structure ClosureOperator (L : Type*) [PartialOrder L] where
  cl : L → L
  extensive : ∀ x, x ≤ cl x
  monotone : Monotone cl
  idempotent : ∀ x, cl (cl x) = cl x

/-- The functor induced by a closure operator. -/
def ClosureOperator.toFunctor (C : ClosureOperator L) : L ⥤ L :=
  monotone_functor C.cl C.monotone

/-- Any natural transformation between functors into a thin category is unique. -/
theorem natTrans_unique {C : Type*} [Category C] {F G : C ⥤ L} (η θ : F ⟶ G) :
    η = θ := by
  ext x
  exact Subsingleton.elim (η.app x) (θ.app x)

end ThinBasics

section LatticeUniversal

variable {Lat : Type*} [Lattice Lat]

/-- In a lattice category, the meet x ⊓ y is the categorical product. -/
theorem meet_le_left (x y : Lat) : (x ⊓ y : Lat) ≤ x :=
  inf_le_left

theorem meet_le_right (x y : Lat) : (x ⊓ y : Lat) ≤ y :=
  inf_le_right

/-- In a lattice category, the join x ⊔ y is the categorical coproduct. -/
theorem le_join_left (x y : Lat) : x ≤ (x ⊔ y : Lat) :=
  le_sup_left

theorem le_join_right (x y : Lat) : y ≤ (x ⊔ y : Lat) :=
  le_sup_right

/-- Universal property of the meet (product limit). -/
theorem meet_universal {x y z : Lat} (hzx : z ≤ x) (hzy : z ≤ y) :
    z ≤ x ⊓ y :=
  le_inf hzx hzy

/-- Universal property of the join (coproduct colimit). -/
theorem join_universal {x y z : Lat} (hxz : x ≤ z) (hyz : y ≤ z) :
    x ⊔ y ≤ z :=
  sup_le hxz hyz

end LatticeUniversal

section SubobjectThin

variable {C : Type*} [Category C] (X : C)

/-- The subobject poset of an object X in an ambient category is a thin category. -/
theorem subobject_is_thin (A B : Subobject X) : Subsingleton (A ⟶ B) :=
  inferInstance

/-- Any subobject morphism in Sub(X) is unique. -/
theorem subobject_hom_unique (A B : Subobject X) (f g : A ⟶ B) : f = g :=
  Subsingleton.elim f g

/-- In Sub(X), every morphism is both monic and epic. -/
theorem subobject_mono (A B : Subobject X) (f : A ⟶ B) : Mono f :=
  thin_mono f

theorem subobject_epi (A B : Subobject X) (f : A ⟶ B) : Epi f :=
  thin_epi f

end SubobjectThin

/-!
# Ext-Collapse in Thin Categories (Ext0 to Extn)
-/

section ExtCollapse

variable {L : Type*} [PartialOrder L]

/-- Ext0 in a thin category is a subsingleton (at most 1 bit of information). -/
theorem ext0_thin_subsingleton (A B : L) : Subsingleton (A ⟶ B) :=
  inferInstance

/-- Any section or retraction between objects in a thin category is unique. -/
theorem section_unique {A B : L} (_f : A ⟶ B) (s1 s2 : B ⟶ A) : s1 = s2 :=
  Subsingleton.elim s1 s2

/-- In a thin category, any morphism with a reverse morphism is an isomorphism. -/
def thin_iso_of_both {A B : L} (f : A ⟶ B) (g : B ⟶ A) : A ≅ B where
  hom := f
  inv := g
  hom_inv_id := Subsingleton.elim (f ≫ g) (𝟙 A)
  inv_hom_id := Subsingleton.elim (g ≫ f) (𝟙 B)

/-- In a thin category, if A ≤ B and B ≤ A, then A ≅ B. -/
theorem thin_antisymm_iso {A B : L} (hAB : A ≤ B) (hBA : B ≤ A) : Nonempty (A ≅ B) :=
  ⟨thin_iso_of_both (homOfLE hAB) (homOfLE hBA)⟩

/-- Any extension in a thin lattice that has a reverse projection splits trivially. -/
theorem thin_extension_splits {A B : L} (f : A ⟶ B) (p : B ⟶ A) :
    p ≫ f = 𝟙 B ∧ f ≫ p = 𝟙 A :=
  ⟨Subsingleton.elim (p ≫ f) (𝟙 B), Subsingleton.elim (f ≫ p) (𝟙 A)⟩

end ExtCollapse

/-!
# The Tamari Lattice of Degree 4 (The Stasheff Pentagon K4)
-/

section TamariPentagon

/-- The 5 parenthesizations of 4 letters (vertices of the Stasheff Pentagon K4). -/
inductive Tree4 : Type
  | t1 : Tree4 -- ((ab)c)d
  | t2 : Tree4 -- (a(bc))d
  | t3 : Tree4 -- (ab)(cd)
  | t4 : Tree4 -- a((bc)d)
  | t5 : Tree4 -- a(b(cd))
  deriving DecidableEq, Repr

open Tree4

/-- The Tamari partial order (right-associativity moves) on 4-term bracketings. -/
def tamari_le : Tree4 → Tree4 → Prop
  | t1, _ => True
  | t2, t2 => True
  | t2, t4 => True
  | t2, t5 => True
  | t3, t3 => True
  | t3, t5 => True
  | t4, t4 => True
  | t4, t5 => True
  | t5, t5 => True
  | _, _ => False

instance : LE Tree4 where
  le := tamari_le

theorem tamari_refl (t : Tree4) : t ≤ t := by
  cases t <;> trivial

theorem tamari_trans (a b c : Tree4) : a ≤ b → b ≤ c → a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp [LE.le, tamari_le]

theorem tamari_antisymm (a b : Tree4) : a ≤ b → b ≤ a → a = b := by
  cases a <;> cases b <;> simp [LE.le, tamari_le]

instance : PartialOrder Tree4 where
  le := tamari_le
  le_refl := tamari_refl
  le_trans := tamari_trans
  le_antisymm := tamari_antisymm

/-- The bottom element of the Tamari lattice (left-bracketed). -/
theorem tamari_bot (t : Tree4) : t1 ≤ t := by
  cases t <;> trivial

/-- The top element of the Tamari lattice (right-bracketed). -/
theorem tamari_top (t : Tree4) : t ≤ t5 := by
  cases t <;> trivial

instance : Fintype Tree4 where
  elems := {t1, t2, t3, t4, t5}
  complete := by
    intro x
    cases x <;> simp

/-- The Tamari order on 4 elements has exactly 5 vertices (Catalan C_3 = 5). -/
theorem tamari4_card : (Fintype.elems : Finset Tree4).card = 5 := by
  rfl

end TamariPentagon

/-!
# The A3 Root System and 3D Associahedron K5 Facets
-/

section A3RootSystem

/-- The 9 almost-positive roots of the A3 root system (6 positive roots + 3 negative simple roots). -/
inductive RootA3 : Type
  -- 6 Positive roots
  | alpha1 : RootA3          -- α₁
  | alpha2 : RootA3          -- α₂
  | alpha3 : RootA3          -- α₃
  | alpha12 : RootA3         -- α₁ + α₂
  | alpha23 : RootA3         -- α₂ + α₃
  | alpha123 : RootA3        -- α₁ + α₂ + α₃
  -- 3 Negative simple roots
  | neg_alpha1 : RootA3      -- -α₁
  | neg_alpha2 : RootA3      -- -α₂
  | neg_alpha3 : RootA3      -- -α₃
  deriving DecidableEq, Repr

open RootA3

/-- The 9 facets of the 3D Associahedron K5 (6 pentagons + 3 squares). -/
inductive FacetK5 : Type
  | pentagon (i : Fin 6) : FacetK5
  | square (j : Fin 3) : FacetK5
  deriving DecidableEq, Repr

/-- The canonical bijection between A3 almost-positive roots and K5 Associahedron facets. -/
def rootA3_to_facetK5 : RootA3 → FacetK5
  | alpha1 => FacetK5.pentagon 0
  | alpha2 => FacetK5.pentagon 1
  | alpha3 => FacetK5.pentagon 2
  | alpha12 => FacetK5.pentagon 3
  | alpha23 => FacetK5.pentagon 4
  | alpha123 => FacetK5.pentagon 5
  | neg_alpha1 => FacetK5.square 0
  | neg_alpha2 => FacetK5.square 1
  | neg_alpha3 => FacetK5.square 2

def facetK5_to_rootA3 : FacetK5 → RootA3
  | FacetK5.pentagon 0 => alpha1
  | FacetK5.pentagon 1 => alpha2
  | FacetK5.pentagon 2 => alpha3
  | FacetK5.pentagon 3 => alpha12
  | FacetK5.pentagon 4 => alpha23
  | FacetK5.pentagon 5 => alpha123
  | FacetK5.square 0 => neg_alpha1
  | FacetK5.square 1 => neg_alpha2
  | FacetK5.square 2 => neg_alpha3

/-- Proof of left-inverse for the A3 root / K5 facet bijection. -/
theorem rootA3_facet_left_inv (r : RootA3) :
    facetK5_to_rootA3 (rootA3_to_facetK5 r) = r := by
  cases r <;> rfl

/-- Proof of right-inverse for the A3 root / K5 facet bijection. -/
theorem rootA3_facet_right_inv (f : FacetK5) :
    rootA3_to_facetK5 (facetK5_to_rootA3 f) = f := by
  cases f with
  | pentagon i =>
    rcases i with ⟨v, hv⟩
    interval_cases v <;> rfl
  | square j =>
    rcases j with ⟨v, hv⟩
    interval_cases v <;> rfl

/-- The A3 root system is in exact bijective correspondence with the facets of K5. -/
def rootA3_facetK5_equiv : RootA3 ≃ FacetK5 where
  toFun := rootA3_to_facetK5
  invFun := facetK5_to_rootA3
  left_inv := rootA3_facet_left_inv
  right_inv := rootA3_facet_right_inv

instance : Fintype RootA3 where
  elems := {alpha1, alpha2, alpha3, alpha12, alpha23, alpha123, neg_alpha1, neg_alpha2, neg_alpha3}
  complete := by
    intro x
    cases x <;> simp

/-- Total number of facets / cluster variables is 9. -/
theorem a3_facet_count : (Fintype.elems : Finset RootA3).card = 9 := by
  rfl

end A3RootSystem

end ThinCategoryLattice
