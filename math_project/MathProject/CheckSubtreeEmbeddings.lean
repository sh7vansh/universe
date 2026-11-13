/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralSubtreeEmbeddings

/-! # Axiom audit and small-case checks for sub-associahedral embeddings -/

open FunctorialGeometry

#print axioms subtreeSupport_iff_mem_partialBracketing
#print axioms subtreeFacet_product_orderIso
#print axioms subtreeSupport_iff_loday_vertex_on_facet
#print axioms globalSubtreeMultiplicity_eq_loday_incidence
#print axioms operadicFactorizationEquiv
#print axioms subtree_fiber_card
#print axioms globalSubtreeMultiplicity_eq_tree_sum
#print axioms globalSubtreeMultiplicity_eq
#print axioms globalSubtreeMultiplicity_k2
#print axioms expectedSubtreeDensity_eq_tree_avg
#print axioms expectedSubtreeDensity_eq_uniform_expectation
#print axioms expectedSubtreeDensity_eq
#print axioms expectedSubtreeDensity_sub_linear_tendsto
#print axioms expectedSubtreeDensity_asymptotic
#print axioms expectedSubtreeDensity_asymptotic_inv

-- K₄ (N = 4): 2-leaf cherry multiplicity Φ(4, 2) = choose 4 2 = 6.
example : globalSubtreeMultiplicity 4 2 = 6 := by
  rw [globalSubtreeMultiplicity_k2 4 (by decide)]
  decide

-- K₅ (N = 5): 2-leaf cherry multiplicity Φ(5, 2) = choose 6 3 = 20.
example : globalSubtreeMultiplicity 5 2 = 20 := by
  rw [globalSubtreeMultiplicity_k2 5 (by decide)]
  decide

-- K₅ (N = 5): 3-leaf subtree multiplicity Φ(5, 3) = C₂ * choose 4 2 = 2 * 6 = 12.
example : globalSubtreeMultiplicity 5 3 = 12 := by
  rw [globalSubtreeMultiplicity_eq 5 3 (by decide) (by decide)]
  norm_num [catalan_two, Nat.choose]

-- Expected cherry density at N = 4 is 6 / 5.
example : expectedSubtreeDensity 4 2 = 6 / 5 := by
  rw [expectedSubtreeDensity_eq 4 2 (by decide) (by decide)]
  norm_num [catalan_one, Nat.choose]

-- In K₅ (n = 3), the interval [0, 3) (k = 3) indexes a square facet K₃ × K₃.
example : Nonempty
    (LodayFacetFaces 3 (subtreeFacetDiagonal 3 0 3 (by decide) (by decide) (by decide)) ≃o
      LodayExposedFace 1 × LodayExposedFace 1) :=
  subtreeFacet_product_orderIso 3 0 3 (by decide) (by decide) (by decide)
