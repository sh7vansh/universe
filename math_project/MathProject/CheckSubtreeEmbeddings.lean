/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralSubtreeEmbeddings
import MathProject.AssociahedralFringeLaw
import MathProject.AssociahedralBoundaryTower

/-! # Axiom audit and small-case checks for associahedral embeddings, fringe laws, and tower -/

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
#print axioms operadicTwoSiteEquiv
#print axioms subtree_two_site_fiber_card
#print axioms globalSubtreePairMultiplicity_eq_zero_of_lt
#print axioms globalSubtreePairMultiplicity_eq
#print axioms subtreeSecondMoment_eq
#print axioms subtreeVariance_k2
#print axioms varianceSlope_pos
#print axioms subtreeVariance_sub_linear_tendsto
#print axioms subtreeVariance_div_tendsto
#print axioms subtreeVariance_asymptotic
#print axioms subtreeDensity_concentration_bound
#print axioms subtreeDensity_concentration_tendsto

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

-- K₃ (N = 3): no tree has two distinct 2-leaf cherries, so Φ₂(3, 2) = 0.
example : globalSubtreePairMultiplicity 3 2 = 0 :=
  globalSubtreePairMultiplicity_eq_zero_of_lt 3 2 (by decide) (by decide)

-- K₄ (N = 4): two distinct 2-leaf cherries give Φ₂(4, 2) = 1 * 1² * choose 2 1 = 2.
example : globalSubtreePairMultiplicity 4 2 = 2 := by
  rw [globalSubtreePairMultiplicity_eq 4 2 (by decide) (by decide)]
  norm_num [catalan_one, Nat.choose]

-- K₃ (N = 3): every tree in T₃ has exactly one cherry, so Var(n₂)(3) = 0.
example : subtreeVariance 3 2 = 0 := by
  rw [subtreeVariance_k2 3 (by decide)]
  norm_num

-- K₄ (N = 4): four trees have 1 cherry and one tree has 2 cherries, so Var(n₂)(4) = 4 / 25.
example : subtreeVariance 4 2 = 4 / 25 := by
  rw [subtreeVariance_k2 4 (by decide)]
  norm_num

-- In K₅ (n = 3), the interval [0, 3) (k = 3) indexes a square facet K₃ × K₃.
example : Nonempty
    (LodayFacetFaces 3 (subtreeFacetDiagonal 3 0 3 (by decide) (by decide) (by decide)) ≃o
      LodayExposedFace 1 × LodayExposedFace 1) :=
  subtreeFacet_product_orderIso 3 0 3 (by decide) (by decide) (by decide)

/-! ## Axiom audits for `AssociahedralFringeLaw` -/

#print axioms ShapeSupport
#print axioms operadicShapeEquiv
#print axioms subtree_shape_fiber_card
#print axioms globalShapeMultiplicity_eq_tree_sum
#print axioms globalShapeMultiplicity_eq
#print axioms expectedShapeDensity_eq_tree_avg
#print axioms expectedShapeDensity_eq_uniform_expectation
#print axioms expectedShapeDensity_eq
#print axioms expectedShapeDensity_sub_linear_tendsto
#print axioms expectedShapeDensity_asymptotic
#print axioms expectedShapeDensity_asymptotic_inv
#print axioms operadicShapeTwoSiteEquiv
#print axioms shape_two_site_fiber_card
#print axioms shape_disjoint_fiber_card
#print axioms globalShapePairMultiplicity_eq_zero_of_lt
#print axioms globalShapePairMultiplicity_eq
#print axioms shapeSecondMoment_eq
#print axioms shapeVariance_eq_sum_sq_sub
#print axioms shapeVariance_nonneg
#print axioms shapeVariance_eq_uniform_expectation
#print axioms shapeVariance_slope_pos
#print axioms shapeVariance_sub_linear_tendsto
#print axioms shapeVariance_div_tendsto
#print axioms shapeVariance_asymptotic
#print axioms shapeDensity_concentration_bound
#print axioms shapeDensity_concentration_tendsto
#print axioms shape_universality_tendsto
#print axioms fringeMass_partialSum_tendsto

/-! ## Axiom audits for `AssociahedralBoundaryTower` -/

#print axioms fullBracketing_two_eq_rootTwo
#print axioms boundaryEmbed
#print axioms boundaryEmbedRight
#print axioms boundaryEmbed_subtreeSupport
#print axioms boundaryEmbed_range
#print axioms boundaryEmbedEquiv
#print axioms boundaryEmbed_preserves_subtreeSupport
#print axioms boundaryEmbed_on_loday_boundaryFacet
#print axioms loday_vertex_on_boundaryFacet_iff
#print axioms boundaryEmbed_preserves_loday_facet_incidence
#print axioms boundaryFacet_orderIso_self
#print axioms boundaryFaceEmbed
#print axioms boundaryFaceEmbed_le_boundaryFacet
#print axioms iteratedBoundaryEmbed_injective
#print axioms iteratedBoundaryEmbed_preserves_subtreeSupport
#print axioms iteratedFaceEmbed_injective
#print axioms iteratedFaceEmbed_le_iff
#print axioms properInternalSpans_card
#print axioms properInternalSpans_total_sum
#print axioms two_dvd_degree_mul_catalan
#print axioms two_mul_associahedronEdgeCount_eq_sum
#print axioms rotationNeighbors_card
#print axioms tamariGraph_degree
#print axioms tamariGraph_edgeCount
#print axioms properInternalSpan_rotation_edge
#print axioms associahedronEdgeCount_le_four_pow
#print axioms four_pow_le_associahedronEdgeCount_mul
#print axioms log_edgeCount_div_tendsto
#print axioms leftEdgeCount_le
#print axioms tamariPartialOrder
#print axioms tamari_chain_length_le
#print axioms quadratic_height_div_edgeCount_tendsto

/-! ## Small-case checks for `AssociahedralFringeLaw` and `AssociahedralBoundaryTower` -/

-- Left-comb and right-comb 3-leaf trees in `FullBracketing 3`.
private def leftComb3 : FullBracketing 3 :=
  ⟨.node () (.node () .nil .nil) .nil, rfl⟩

private def rightComb3 : FullBracketing 3 :=
  ⟨.node () .nil (.node () .nil .nil), rfl⟩

-- Both 3-leaf shapes have identical global multiplicity Φ_S(4) = choose 2 1 = 2 in K₄.
example : globalShapeMultiplicity 4 leftComb3 = 2 := by
  rw [globalShapeMultiplicity_eq 4 (by decide) (by decide) leftComb3]
  decide

example : globalShapeMultiplicity 4 rightComb3 = 2 := by
  rw [globalShapeMultiplicity_eq 4 (by decide) (by decide) rightComb3]
  decide

example : globalShapeMultiplicity 4 leftComb3 = globalShapeMultiplicity 4 rightComb3 := by
  rw [globalShapeMultiplicity_eq 4 (by decide) (by decide) leftComb3,
    globalShapeMultiplicity_eq 4 (by decide) (by decide) rightComb3]

-- Both 3-leaf shapes have identical global multiplicity Φ_S(5) = choose 4 2 = 6 in K₅.
example : globalShapeMultiplicity 5 leftComb3 = 6 := by
  rw [globalShapeMultiplicity_eq 5 (by decide) (by decide) leftComb3]
  decide

example : globalShapeMultiplicity 5 rightComb3 = 6 := by
  rw [globalShapeMultiplicity_eq 5 (by decide) (by decide) rightComb3]
  decide

example : globalShapeMultiplicity 5 leftComb3 = globalShapeMultiplicity 5 rightComb3 := by
  rw [globalShapeMultiplicity_eq 5 (by decide) (by decide) leftComb3,
    globalShapeMultiplicity_eq 5 (by decide) (by decide) rightComb3]

-- Associahedron edge counts: K₄ has 5 edges (pentagon), K₅ has 21 edges.
example : associahedronEdgeCount 4 = 5 := by
  have hc : catalan 3 = 5 := by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]
    decide
  simp [associahedronEdgeCount, hc]

example : associahedronEdgeCount 5 = 21 := by
  have hc : catalan 4 = 14 := by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]
    decide
  simp [associahedronEdgeCount, hc]

-- In K₄ (N = 4), every tree has 4 - 2 = 2 proper internal spans.
example (T : FullBracketing 4) : (properInternalSpans T).card = 2 :=
  properInternalSpans_card (by decide) T

-- Boundary embedding K₃ ↪ K₄ sends `leftComb3` to a 4-leaf tree with subtree support [0, 3).
example :
    (boundaryEmbed 3 (by decide) leftComb3).val =
      .node () (.node () (.node () .nil .nil) .nil) .nil :=
  rfl

example : SubtreeSupport (boundaryEmbed 3 (by decide) leftComb3) 0 3 :=
  boundaryEmbed_subtreeSupport 3 (by decide) leftComb3

-- Small Tamari chain check: `leftComb3 < rightComb3` in K₃ satisfies L = 1 ≤ 1.
example :
    let c : Fin 2 → FullBracketing 3 := ![leftComb3, rightComb3]
    (∀ i : Fin 1, TamariLT (c i.castSucc) (c i.succ)) ∧
      (1 : ℕ) ≤ (3 - 1) * (3 - 2) / 2 := by
  refine ⟨fun i => ?_, by decide⟩
  fin_cases i
  exact ⟨Relation.ReflTransGen.single (RightRotation.root .nil .nil .nil), by
    intro h
    have hv := congrArg Subtype.val h
    simp [leftComb3, rightComb3] at hv⟩

-- Small check of `tamari_chain_length_le` on a length-1 chain in K₄ (L ≤ 3).
example : 1 ≤ (4 - 1) * (4 - 2) / 2 ∧ 1 ≤ 4 * (4 - 1) / 2 := by
  let t₀ : FullBracketing 4 := boundaryEmbed 3 (by decide) leftComb3
  let t₁ : FullBracketing 4 := boundaryEmbed 3 (by decide) rightComb3
  let c : Fin 2 → FullBracketing 4 := ![t₀, t₁]
  have hc : ∀ i : Fin 1, TamariLT (c i.castSucc) (c i.succ) := by
    intro i
    fin_cases i
    refine ⟨Relation.ReflTransGen.single
      (RightRotation.left (RightRotation.root .nil .nil .nil) .nil), ?_⟩
    intro h
    have hv : BinaryTree.node () leftComb3.val .nil =
        BinaryTree.node () rightComb3.val .nil := congrArg Subtype.val h
    simp [leftComb3, rightComb3] at hv
  exact tamari_chain_length_le c hc
