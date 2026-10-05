/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.FunctorialGeometry

/-! # Axiom audit and facet shape checks -/

open FunctorialGeometry

#print axioms facet_arities
#print axioms polygonFacet_product_orderIso
#print axioms Loday_facet_geometric_product_orderIso
#print axioms K5_pentagonal_facet_iff
#print axioms K5_square_facet_iff
#print axioms Loday_K5_pentagonal_facet
#print axioms Loday_K5_square_facet
#print axioms Loday_K5_pentagonal_facet_count
#print axioms Loday_K5_square_facet_count
#print axioms rootAn_lodayFacet_equiv
#print axioms rootA3_geometric_pentagonal_facet
#print axioms rootA3_geometric_square_facet

-- The two orientations of the pentagonal cut: triangle/pentagon and pentagon/triangle.
example : facetLeftArity (diagonal_polygon_equiv 3
    (rootA3_to_diagonal_3 RootA3.neg_alpha1)) = 2 ∧
    facetRightArity (diagonal_polygon_equiv 3
      (rootA3_to_diagonal_3 RootA3.neg_alpha1)) = 4 := by decide

example : facetLeftArity (diagonal_polygon_equiv 3
    (rootA3_to_diagonal_3 RootA3.alpha123)) = 4 ∧
    facetRightArity (diagonal_polygon_equiv 3
      (rootA3_to_diagonal_3 RootA3.alpha123)) = 2 := by decide

-- Pentagon and square labels now imply actual convex facet face orders.
example : Nonempty (LodayFacetFaces 3
    (diagonal_polygon_equiv 3 (rootA3_to_diagonal_3 RootA3.neg_alpha1)) ≃o
      LodayExposedFace 2) :=
  rootA3_geometric_pentagonal_facet RootA3.neg_alpha1 0 rfl

example : Nonempty (LodayFacetFaces 3
    (diagonal_polygon_equiv 3 (rootA3_to_diagonal_3 RootA3.neg_alpha2)) ≃o
      (LodayExposedFace 1 × LodayExposedFace 1)) :=
  rootA3_geometric_square_facet RootA3.neg_alpha2 0 rfl
