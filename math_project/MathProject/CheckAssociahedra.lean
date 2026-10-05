/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.FunctorialGeometry

/-! # Axiom audit and small-case checks for the general geometric theorem -/

open FunctorialGeometry

#print axioms spanFamily_complete
#print axioms treeSpans_injective
#print axioms fullBracketing_vertex_equiv
#print axioms treeSpans_rotate_away
#print axioms treeIntervalSum_eq_iff
#print axioms LodayPolytope_extremePoints
#print axioms tree_normal_certificate
#print axioms polygon_loday_face_orderIso
#print axioms Loday_affine_dimension
#print axioms Loday_geometric_vertex_count_formula
#print axioms Loday_geometric_facet_count
#print axioms all_Kn_geometric_orderIso
#print axioms all_Kn_poset_realization

-- K₂: a point, with one extreme point and no proper facets.
example : (LodayAffineDimension 0,
    Fintype.card ↥((LodayPolytope 0).extremePoints ℝ),
    Fintype.card {F : LodayExposedFace 0 // IsCoatom F}) = (0, 1, 0) := by
  rw [Loday_affine_dimension, Loday_geometric_vertex_count_formula, Loday_geometric_facet_count]
  norm_num [Nat.choose]

-- K₃: an interval, with two extreme points and two facets.
example : (LodayAffineDimension 1,
    Fintype.card ↥((LodayPolytope 1).extremePoints ℝ),
    Fintype.card {F : LodayExposedFace 1 // IsCoatom F}) = (1, 2, 2) := by
  rw [Loday_affine_dimension, Loday_geometric_vertex_count_formula, Loday_geometric_facet_count]
  norm_num [Nat.choose]

-- K₄: the pentagon, with five extreme points and five facets.
example : (LodayAffineDimension 2,
    Fintype.card ↥((LodayPolytope 2).extremePoints ℝ),
    Fintype.card {F : LodayExposedFace 2 // IsCoatom F}) = (2, 5, 5) := by
  rw [Loday_affine_dimension, Loday_geometric_vertex_count_formula, Loday_geometric_facet_count]
  norm_num [Nat.choose]

-- K₅: dimension three, with fourteen extreme points and nine facets.
example : (LodayAffineDimension 3,
    Fintype.card ↥((LodayPolytope 3).extremePoints ℝ),
    Fintype.card {F : LodayExposedFace 3 // IsCoatom F}) = (3, 14, 9) := by
  rw [Loday_affine_dimension, Loday_geometric_vertex_count_formula, Loday_geometric_facet_count]
  norm_num [Nat.choose]
