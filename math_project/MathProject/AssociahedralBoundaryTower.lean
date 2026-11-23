/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralSubtreeEmbeddings
import MathProject.AssociahedralStructuralBridges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Associahedral Boundary Tower, Edge Regularity, and K_∞ Growth

This module formalizes:

1. **Inductive Boundary Tower (`K_N ↪ K_{N+1}`):**
   - Specialization of `operadicFactorizationEquiv` at `k = N` (`2 ≤ N`), giving explicit
     tree-level boundary embeddings `boundaryEmbed` (left facet `[0, N)`) and
     `boundaryEmbedRight` (right facet `[1, N + 1)`), with image
     `{ T // SubtreeSupport T 0 N }`, preserving Loday coordinates and Loday facet incidence.
   - Specialization of `Loday_facet_geometric_product_orderIso` at `k = N` (`K_N × K_2`)
     together with `Unique (LodayExposedFace 0)` to prove `boundaryFacet_orderIso_self`:
     the boundary facet `[0, N)` of `K_{N+1}` is order-isomorphic to `K_N`.
   - Iterated embeddings `iteratedBoundaryEmbed : FullBracketing N ↪ FullBracketing (N + m)` and
     `iteratedFaceEmbed : LodayExposedFace n ↪o LodayExposedFace (n + m)` along the tower.

2. **Edge Count, `(N - 2)`-Regularity, and Exponential-vs-Quadratic `K_∞` Growth:**
   - Exact per-vertex degree count `properInternalSpans_card` (`= N - 2`) using `treeSpans`,
     plus `(N - 2)`-regularity of the Tamari rotation graph `tamariGraph N`.
   - Exact double-counting identity `∑ T, (properInternalSpans T).card = (N - 2) * catalan (N - 1)`,
     parity `2 ∣ (N - 2) * catalan (N - 1)`, and `associahedronEdgeCount N`.
   - Asymptotic exponential horizontal growth
     `Real.log (associahedronEdgeCount N) / ((N - 1) * Real.log 4) → 1`
     via central binomial bounds `4^m / (2m + 1) ≤ choose (2m) m ≤ 4^m`.
   - Exact Tamari partial order on `FullBracketing N` via `ReflTransGen RightRotation`,
     quadratic chain-length bound `(N - 1) * (N - 2) / 2 ≤ N * (N - 1) / 2` via `leftEdgeCount`,
     and `(N * (N - 1) / 2 : ℝ) / associahedronEdgeCount N → 0` as `N → ∞`.
-/

namespace FunctorialGeometry

open Filter Topology

section BoundaryInclusion

/-- The unique full binary bracketing of `2` leaves. -/
def rootTwo : FullBracketing 2 :=
  ⟨.node () .nil .nil, rfl⟩

private theorem fullBracketing_eq_node_nil_nil {m : ℕ} (hm : m = 2) (t : FullBracketing m) :
    t.val = .node () .nil .nil := by
  cases h : t.val with
  | nil =>
    have hp := t.property
    simp [h, BinaryTree.numLeaves] at hp
    omega
  | node val l r =>
    cases val
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    have hp := t.property
    simp [h, BinaryTree.numLeaves] at hp
    have hl1 : l.numLeaves = 1 := by omega
    have hr1 : r.numLeaves = 1 := by omega
    have hl_nil : l = .nil := by
      cases l with
      | nil => rfl
      | node _ a b =>
        have ha := a.numLeaves_pos
        have hb := b.numLeaves_pos
        simp [BinaryTree.numLeaves] at hl1
        omega
    have hr_nil : r = .nil := by
      cases r with
      | nil => rfl
      | node _ a b =>
        have ha := a.numLeaves_pos
        have hb := b.numLeaves_pos
        simp [BinaryTree.numLeaves] at hr1
        omega
    simp [hl_nil, hr_nil]

theorem fullBracketing_two_eq_rootTwo (t : FullBracketing 2) : t = rootTwo :=
  Subtype.ext (fullBracketing_eq_node_nil_nil rfl t)

instance : Unique (FullBracketing 2) where
  default := rootTwo
  uniq := fullBracketing_two_eq_rootTwo

private def rootTwoOuter (N : ℕ) (_hN : 2 ≤ N) : FullBracketing (N + 1 - N + 1) :=
  ⟨.node () .nil .nil, by simp [BinaryTree.numLeaves]⟩

/-- Left boundary embedding `K_N ↪ K_{N+1}` sending `T` to the facet `[0, N)`
via `operadicFactorizationEquiv (N + 1) N 0` with outer tree `rootTwo`. -/
def boundaryEmbed (N : ℕ) (hN : 2 ≤ N) :
    FullBracketing N ↪ FullBracketing (N + 1) where
  toFun T := (operadicFactorizationEquiv (N + 1) N 0 hN (by omega) (rootTwoOuter N hN, T)).val
  inj' T₁ T₂ h := by
    have hsub : operadicFactorizationEquiv (N + 1) N 0 hN (by omega) (rootTwoOuter N hN, T₁) =
        operadicFactorizationEquiv (N + 1) N 0 hN (by omega) (rootTwoOuter N hN, T₂) :=
      Subtype.ext h
    have hinj := (operadicFactorizationEquiv (N + 1) N 0 hN (by omega)).injective hsub
    exact congrArg Prod.snd hinj

/-- Right boundary embedding `K_N ↪ K_{N+1}` sending `T` to the facet `[1, N + 1)`. -/
def boundaryEmbedRight (N : ℕ) (hN : 2 ≤ N) :
    FullBracketing N ↪ FullBracketing (N + 1) where
  toFun T := (operadicFactorizationEquiv (N + 1) N 1 hN (by omega) (rootTwoOuter N hN, T)).val
  inj' T₁ T₂ h := by
    have hsub : operadicFactorizationEquiv (N + 1) N 1 hN (by omega) (rootTwoOuter N hN, T₁) =
        operadicFactorizationEquiv (N + 1) N 1 hN (by omega) (rootTwoOuter N hN, T₂) :=
      Subtype.ext h
    have hinj := (operadicFactorizationEquiv (N + 1) N 1 hN (by omega)).injective hsub
    exact congrArg Prod.snd hinj

@[simp]
theorem boundaryEmbed_val (N : ℕ) (hN : 2 ≤ N) (T : FullBracketing N) :
    (boundaryEmbed N hN T).val = .node () T.val .nil := rfl

@[simp]
theorem boundaryEmbedRight_val (N : ℕ) (hN : 2 ≤ N) (T : FullBracketing N) :
    (boundaryEmbedRight N hN T).val = .node () .nil T.val := rfl

theorem boundaryEmbed_subtreeSupport (N : ℕ) (hN : 2 ≤ N) (T : FullBracketing N) :
    SubtreeSupport (boundaryEmbed N hN T) 0 N :=
  (operadicFactorizationEquiv (N + 1) N 0 hN (by omega) (rootTwoOuter N hN, T)).property

theorem boundaryEmbedRight_subtreeSupport (N : ℕ) (hN : 2 ≤ N) (T : FullBracketing N) :
    SubtreeSupport (boundaryEmbedRight N hN T) 1 N :=
  (operadicFactorizationEquiv (N + 1) N 1 hN (by omega) (rootTwoOuter N hN, T)).property

/-- The image of `boundaryEmbed N hN` is precisely
`{ T : FullBracketing (N + 1) | SubtreeSupport T 0 N }`. -/
theorem boundaryEmbed_range (N : ℕ) (hN : 2 ≤ N) :
    Set.range (boundaryEmbed N hN) =
      { T : FullBracketing (N + 1) | SubtreeSupport T 0 N } := by
  ext T
  constructor
  · rintro ⟨S, rfl⟩
    exact boundaryEmbed_subtreeSupport N hN S
  · intro hT
    let p := (operadicFactorizationEquiv (N + 1) N 0 hN (by omega)).symm ⟨T, hT⟩
    refine ⟨p.2, ?_⟩
    have hp1 : p.1 = rootTwoOuter N hN := by
      apply Subtype.ext
      exact fullBracketing_eq_node_nil_nil (by omega) p.1
    have happ : operadicFactorizationEquiv (N + 1) N 0 hN (by omega) p = ⟨T, hT⟩ :=
      (operadicFactorizationEquiv (N + 1) N 0 hN (by omega)).apply_symm_apply ⟨T, hT⟩
    have hval := congrArg Subtype.val happ
    simpa only [boundaryEmbed, Function.Embedding.coeFn_mk, ← hp1] using hval

/-- Equivalence between `FullBracketing N` and the boundary facet trees `[0, N)`. -/
def boundaryEmbedEquiv (N : ℕ) (hN : 2 ≤ N) :
    FullBracketing N ≃ { T : FullBracketing (N + 1) // SubtreeSupport T 0 N } where
  toFun T := ⟨boundaryEmbed N hN T, boundaryEmbed_subtreeSupport N hN T⟩
  invFun T := ((operadicFactorizationEquiv (N + 1) N 0 hN (by omega)).symm T).2
  left_inv T := by
    have h := (operadicFactorizationEquiv (N + 1) N 0 hN (by omega)).left_inv
      (rootTwoOuter N hN, T)
    exact congrArg Prod.snd h
  right_inv T := by
    apply Subtype.ext
    let p := (operadicFactorizationEquiv (N + 1) N 0 hN (by omega)).symm T
    have hp1 : p.1 = rootTwoOuter N hN := by
      apply Subtype.ext
      exact fullBracketing_eq_node_nil_nil (by omega) p.1
    have happ : operadicFactorizationEquiv (N + 1) N 0 hN (by omega) p = T :=
      (operadicFactorizationEquiv (N + 1) N 0 hN (by omega)).apply_symm_apply T
    have hval := congrArg Subtype.val happ
    simpa only [boundaryEmbed, Function.Embedding.coeFn_mk, ← hp1] using hval

theorem boundaryEmbed_treeSpans (N : ℕ) (hN : 2 ≤ N) (T : FullBracketing N) :
    treeSpans (boundaryEmbed N hN T).val 0 =
      insert (0, N + 1) (treeSpans T.val 0) := by
  simp [boundaryEmbed_val, treeSpans, T.property, BinaryTree.numLeaves]

theorem boundaryEmbed_preserves_subtreeSupport {N i k : ℕ} (hN : 2 ≤ N)
    (_hk : 2 ≤ k) (hi : i + k ≤ N) (T : FullBracketing N) :
    SubtreeSupport (boundaryEmbed N hN T) i k ↔ SubtreeSupport T i k := by
  change (i, i + k) ∈ treeSpans (boundaryEmbed N hN T).val 0 ↔ (i, i + k) ∈ treeSpans T.val 0
  rw [boundaryEmbed_treeSpans N hN T, Finset.mem_insert]
  constructor
  · rintro (hroot | hmem)
    · have h2 := congrArg Prod.snd hroot
      omega
    · exact hmem
  · exact Or.inr

/-- The boundary diagonal `[0, n + 2)` of `K_{n+3}`. -/
def boundaryFacetDiagonal (n : ℕ) : PolygonDiagonal (n + 3) :=
  subtreeFacetDiagonal (n + 1) 0 (n + 2) (by omega) (by omega) (by omega)

/-- Every embedded vertex `boundaryEmbed (n + 2) _ T` lies on the Loday
boundary facet `[0, n + 2)`. -/
theorem boundaryEmbed_on_loday_boundaryFacet (n : ℕ) (T : FullBracketing (n + 2)) :
    lodayPoint (n + 1) (boundaryEmbed (n + 2) (by omega) T) ∈
      (polygon_loday_face_orderIso (n + 1)
        (singletonPolygonFace (boundaryFacetDiagonal n))).val := by
  dsimp [boundaryFacetDiagonal]
  rw [← subtreeSupport_iff_loday_vertex_on_facet (n + 1) 0 (n + 2)
    (by omega) (by omega) (by omega)]
  exact boundaryEmbed_subtreeSupport (n + 2) (by omega) T

/-- Conversely, a Loday vertex of `K_{n+3}` lies on `[0, n + 2)` iff it is in
`Set.range (boundaryEmbed (n + 2) _)`. -/
theorem loday_vertex_on_boundaryFacet_iff (n : ℕ) (T : FullBracketing (n + 3)) :
    lodayPoint (n + 1) T ∈
        (polygon_loday_face_orderIso (n + 1)
          (singletonPolygonFace (boundaryFacetDiagonal n))).val ↔
      T ∈ Set.range (boundaryEmbed (n + 2) (by omega)) := by
  dsimp [boundaryFacetDiagonal]
  rw [← subtreeSupport_iff_loday_vertex_on_facet (n + 1) 0 (n + 2)
    (by omega) (by omega) (by omega), boundaryEmbed_range (n + 2) (by omega)]
  rfl

/-- `boundaryEmbed` preserves incidence with every proper Loday facet `[i, i + k)` of `K_{n+2}`. -/
theorem boundaryEmbed_preserves_loday_facet_incidence (n i k : ℕ)
    (hk : 2 ≤ k) (hkN : k < n + 2) (hi : i + k ≤ n + 2) (T : FullBracketing (n + 2)) :
    lodayPoint n T ∈
        (polygon_loday_face_orderIso n
          (singletonPolygonFace (subtreeFacetDiagonal n i k hk hkN hi))).val ↔
      lodayPoint (n + 1) (boundaryEmbed (n + 2) (by omega) T) ∈
        (polygon_loday_face_orderIso (n + 1)
          (singletonPolygonFace
            (subtreeFacetDiagonal (n + 1) i k hk (by omega) (by omega)))).val := by
  rw [← subtreeSupport_iff_loday_vertex_on_facet n i k hk hkN hi T,
    ← subtreeSupport_iff_loday_vertex_on_facet (n + 1) i k hk (by omega) (by omega)
      (boundaryEmbed (n + 2) (by omega) T),
    boundaryEmbed_preserves_subtreeSupport (by omega) hk hi T]

theorem boundaryEmbed_lodayPoint_castSucc (n : ℕ) (T : FullBracketing (n + 2))
    (i : Fin (n + 1)) :
    lodayPoint (n + 1) (boundaryEmbed (n + 2) (by omega) T) i.castSucc = lodayPoint n T i := by
  change (treeGapWeight (boundaryEmbed (n + 2) (by omega) T).val 0 i.val : ℝ) =
    (treeGapWeight T.val 0 i.val : ℝ)
  rw [boundaryEmbed_val]
  have hne : i.val ≠ 0 + T.val.numLeaves - 1 := by
    rw [T.property]
    have hi := i.isLt
    omega
  simp only [treeGapWeight]
  split_ifs with h
  · exact absurd h hne
  · simp

theorem boundaryEmbed_lodayPoint_last (n : ℕ) (T : FullBracketing (n + 2)) :
    lodayPoint (n + 1) (boundaryEmbed (n + 2) (by omega) T) (Fin.last (n + 1)) = n + 2 := by
  change (treeGapWeight (boundaryEmbed (n + 2) (by omega) T).val 0 (n + 1) : ℝ) = n + 2
  rw [boundaryEmbed_val]
  have h := treeGapWeight_root T.val .nil 0
  simp only [Nat.zero_add, T.property, BinaryTree.numLeaves, mul_one] at h
  have heq : 0 + (n + 2) - 1 = n + 1 := by omega
  rw [← heq]
  have h' : treeGapWeight (.node () T.val .nil) 0 (0 + (n + 2) - 1) = n + 2 := by
    simpa [T.property] using h
  rw [h']
  push_cast
  rfl

private theorem no_properBracket_two (p : ProperBracket 2) : False := by
  have h1 := p.length_two
  have h2 := p.right.isLt
  have h3 := p.proper
  omega

private theorem partialBracketing_two_subsingleton : Subsingleton (PartialBracketing 2) := by
  constructor
  intro p q
  apply Subtype.ext
  have hemp : ∀ r : PartialBracketing 2, r.val = ∅ := by
    intro r
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b _
    exact no_properBracket_two b
  exact (hemp p).trans (hemp q).symm

instance : Unique (LodayExposedFace 0) where
  default := wholeLodayFace 0
  uniq F := by
    have iso : PartialBracketing 2 ≃o LodayExposedFace 0 :=
      partialBracketing_loday_orderIso 0
    have : Subsingleton (PartialBracketing 2) := partialBracketing_two_subsingleton
    have hF := Subsingleton.elim (iso.symm F) (iso.symm (wholeLodayFace 0))
    exact iso.symm.injective hF

private def prodUniqueRightOrderIso (A B : Type*) [PartialOrder A] [PartialOrder B] [Unique B] :
    A × B ≃o A where
  toFun p := p.1
  invFun a := (a, default)
  left_inv p := Prod.ext rfl (Unique.uniq _ p.2).symm
  right_inv _ := rfl
  map_rel_iff' := by
    intro p q
    have hp : p.2 = default := Unique.uniq _ p.2
    have hq : q.2 = default := Unique.uniq _ q.2
    simp [Prod.le_def, hp, hq]

/-- **Boundary Facet Order Isomorphism (`K_N ≅ [0, N) ⊂ K_{N+1}`):**
For `2 ≤ N`, the boundary facet `[0, N)` of `LodayPolytope (N - 1)` (`K_{N+1}`) is
order-isomorphic to `LodayExposedFace (N - 2)` (`K_N`). -/
noncomputable def boundaryFacet_orderIso_self (N : ℕ) (hN : 2 ≤ N) :
    LodayFacetFaces (N - 1)
        (subtreeFacetDiagonal (N - 1) 0 N hN (by omega) (by omega)) ≃o
      LodayExposedFace (N - 2) := by
  have iso := Loday_facet_geometric_product_orderIso (N - 1)
    (subtreeFacetDiagonal (N - 1) 0 N hN (by omega) (by omega))
  rw [subtreeFacet_leftArity, subtreeFacet_rightArity] at iso
  have hr : (N - 1) + 2 - N + 1 - 2 = 0 := by omega
  rw [hr] at iso
  exact iso.trans (prodUniqueRightOrderIso (LodayExposedFace (N - 2)) (LodayExposedFace 0))

/-- Order-embedding of the face poset of `K_{n+2}` as the boundary facet `[0, n+2)` of
`K_{n+3}`. -/
noncomputable def boundaryFaceEmbed (n : ℕ) :
    LodayExposedFace n ↪o LodayExposedFace (n + 1) :=
  let iso : LodayExposedFace n ≃o LodayFacetFaces (n + 1) (boundaryFacetDiagonal n) :=
    (boundaryFacet_orderIso_self (n + 2) (by omega)).symm
  iso.toOrderEmbedding.trans (OrderEmbedding.subtype _)

theorem boundaryFaceEmbed_le_boundaryFacet (n : ℕ) (F : LodayExposedFace n) :
    boundaryFaceEmbed n F ≤
      polygon_loday_face_orderIso (n + 1) (singletonPolygonFace (boundaryFacetDiagonal n)) :=
  ((boundaryFacet_orderIso_self (n + 2) (by omega)).symm F).property

/-- Iterated tree-level boundary embedding `K_N ↪ K_{N+m}` along the tower. -/
def iteratedBoundaryEmbed (N m : ℕ) (hN : 2 ≤ N) :
    FullBracketing N ↪ FullBracketing (N + m) :=
  match m with
  | 0 => Function.Embedding.refl _
  | m + 1 => (iteratedBoundaryEmbed N m hN).trans (boundaryEmbed (N + m) (by omega))

@[simp]
theorem iteratedBoundaryEmbed_zero (N : ℕ) (hN : 2 ≤ N) (T : FullBracketing N) :
    iteratedBoundaryEmbed N 0 hN T = T := rfl

@[simp]
theorem iteratedBoundaryEmbed_succ (N m : ℕ) (hN : 2 ≤ N) (T : FullBracketing N) :
    iteratedBoundaryEmbed N (m + 1) hN T =
      boundaryEmbed (N + m) (by omega) (iteratedBoundaryEmbed N m hN T) := rfl

theorem iteratedBoundaryEmbed_injective (N m : ℕ) (hN : 2 ≤ N) :
    Function.Injective (iteratedBoundaryEmbed N m hN) :=
  (iteratedBoundaryEmbed N m hN).injective

theorem iteratedBoundaryEmbed_preserves_subtreeSupport {N m i k : ℕ} (hN : 2 ≤ N)
    (hk : 2 ≤ k) (hi : i + k ≤ N) (T : FullBracketing N) :
    SubtreeSupport (iteratedBoundaryEmbed N m hN T) i k ↔ SubtreeSupport T i k := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iteratedBoundaryEmbed_succ,
      boundaryEmbed_preserves_subtreeSupport (by omega) hk (by omega), ih]

theorem iteratedBoundaryEmbed_subtreeSupport (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m)
    (T : FullBracketing N) :
    SubtreeSupport (iteratedBoundaryEmbed N m hN T) 0 N := by
  cases m with
  | zero => omega
  | succ m =>
    rw [iteratedBoundaryEmbed_succ]
    have hs : SubtreeSupport (iteratedBoundaryEmbed N m hN T) 0 N := by
      cases m with
      | zero =>
        rw [iteratedBoundaryEmbed_zero]
        dsimp [SubtreeSupport]
        have hroot := treeSpans_root 0 (by rw [T.property]; exact hN)
        rwa [T.property] at hroot
      | succ k =>
        exact (iteratedBoundaryEmbed_preserves_subtreeSupport hN hN (by omega) T).mpr (by
          dsimp [SubtreeSupport]
          have hroot := treeSpans_root 0 (by rw [T.property]; exact hN)
          rwa [T.property] at hroot)
    exact (boundaryEmbed_preserves_subtreeSupport (by omega) hN (by omega) _).mpr hs

/-- Iterated order-embedding of face posets `LodayExposedFace n ↪o LodayExposedFace (n + m)`. -/
noncomputable def iteratedFaceEmbed (n m : ℕ) :
    LodayExposedFace n ↪o LodayExposedFace (n + m) :=
  match m with
  | 0 => RelEmbedding.refl (· ≤ ·)
  | m + 1 => (iteratedFaceEmbed n m).trans (boundaryFaceEmbed (n + m))

@[simp]
theorem iteratedFaceEmbed_zero (n : ℕ) (F : LodayExposedFace n) :
    iteratedFaceEmbed n 0 F = F := rfl

@[simp]
theorem iteratedFaceEmbed_succ (n m : ℕ) (F : LodayExposedFace n) :
    iteratedFaceEmbed n (m + 1) F = boundaryFaceEmbed (n + m) (iteratedFaceEmbed n m F) := rfl

theorem iteratedFaceEmbed_injective (n m : ℕ) :
    Function.Injective (iteratedFaceEmbed n m) :=
  (iteratedFaceEmbed n m).injective

theorem iteratedFaceEmbed_le_iff (n m : ℕ) (F G : LodayExposedFace n) :
    iteratedFaceEmbed n m F ≤ iteratedFaceEmbed n m G ↔ F ≤ G :=
  (iteratedFaceEmbed n m).le_iff_le

end BoundaryInclusion

section EdgeRegularityAndDoubleCounting

/-- Uniform `Fintype` instance on `FullBracketing n` for every `n : ℕ`. -/
@[instance_reducible]
private def instFintypeFullBracketingBoundary : (n : ℕ) → Fintype (FullBracketing n)
  | 0 => @Fintype.ofIsEmpty _ ⟨no_nullary_fullBracketing⟩
  | _ + 1 => inferInstance

attribute [local instance] instFintypeFullBracketingBoundary

private theorem fullBracketing_card_pos_arity (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (FullBracketing n) = catalan (n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    rw [Nat.add_sub_cancel]
    exact fullBracketing_card m

/-- Proper internal spans of `T : FullBracketing N` (`2 ≤ p.2 - p.1 ≤ N - 1`).
Each proper internal span corresponds to a rotatable internal edge of `T`. -/
def properInternalSpans {N : ℕ} (T : FullBracketing N) : Finset BracketSpan :=
  (treeSpans T.val 0).filter (fun p => 2 ≤ p.2 - p.1 ∧ p.2 - p.1 ≤ N - 1)

theorem properInternalSpans_eq_treeProperSpans {N : ℕ} (hN : 2 ≤ N) (T : FullBracketing N) :
    properInternalSpans T = treeProperSpans T := by
  ext p
  simp only [properInternalSpans, treeProperSpans, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hp, _, hle⟩
    refine ⟨?_, hp⟩
    intro hroot
    have h1 := congrArg Prod.fst hroot
    have h2 := congrArg Prod.snd hroot
    dsimp at h1 h2
    omega
  · rintro ⟨hne, hp⟩
    have hv := treeSpans_valid T.val 0 p hp
    dsimp [SpanValid] at hv
    rw [T.property, Nat.zero_add] at hv
    refine ⟨hp, by omega, ?_⟩
    by_contra hgt
    apply hne
    ext <;> omega

/-- Every tree `T : FullBracketing N` (`2 ≤ N`, and in particular `3 ≤ N`) has
exactly `N - 2` proper internal spans. -/
theorem properInternalSpans_card {N : ℕ} (hN : 2 ≤ N) (T : FullBracketing N) :
    (properInternalSpans T).card = N - 2 := by
  rw [properInternalSpans_eq_treeProperSpans hN T, ← treePartialBracketing_spans,
    properBracketSpans_card, treeProperSpans_card hN T]

/-- Double-counting the incidence between trees and proper internal spans:
the total number of proper internal spans over `FullBracketing N` is `(N - 2) * C_{N-1}`. -/
theorem properInternalSpans_total_sum (N : ℕ) (hN : 2 ≤ N) :
    ∑ T : FullBracketing N, (properInternalSpans T).card = (N - 2) * catalan (N - 1) := by
  have hconst : ∀ T : FullBracketing N, (properInternalSpans T).card = N - 2 :=
    fun T => properInternalSpans_card hN T
  simp_rw [hconst, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    fullBracketing_card_pos_arity N (by omega), mul_comm]

/-- For every `N`, `2` divides `(N - 2) * catalan (N - 1)`. -/
theorem two_dvd_degree_mul_catalan (N : ℕ) :
    2 ∣ (N - 2) * catalan (N - 1) := by
  by_cases hN : N ≤ 2
  · have h0 : N - 2 = 0 := by omega
    rw [h0, zero_mul]
    exact dvd_zero 2
  · have hN3 : 3 ≤ N := by omega
    rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h2 : 2 ∣ N - 2 := ⟨k - 1, by omega⟩
      exact dvd_mul_of_dvd_left h2 _
    · have hcb_even : 2 ∣ Nat.centralBinom (N - 1) := by
        have hch := Nat.choose_succ_succ (2 * (N - 1) - 1) (N - 2)
        have hm1 : (N - 2).succ = N - 1 := by omega
        have h2m : (2 * (N - 1) - 1).succ = 2 * (N - 1) := by omega
        have hsym : Nat.choose (2 * (N - 1) - 1) (N - 1) =
            Nat.choose (2 * (N - 1) - 1) (N - 2) := by
          have hle : N - 1 ≤ 2 * (N - 1) - 1 := by omega
          rw [← Nat.choose_symm hle]
          congr 1
          omega
        rw [hm1, h2m, ← Nat.centralBinom_eq_two_mul_choose, hsym] at hch
        exact ⟨Nat.choose (2 * (N - 1) - 1) (N - 2), by omega⟩
      have hmul : N * catalan (N - 1) = Nat.centralBinom (N - 1) := by
        have h := succ_mul_catalan_eq_centralBinom (N - 1)
        rwa [Nat.sub_add_cancel (by omega)] at h
      rw [← hmul] at hcb_even
      have hcop : Nat.Coprime 2 N := by
        rw [hk]
        simp
      exact dvd_mul_of_dvd_right (hcop.dvd_of_dvd_mul_left hcb_even) _

/-- Number of undirected edges of the associahedron `K_N`. -/
def associahedronEdgeCount (N : ℕ) : ℕ :=
  ((N - 2) * catalan (N - 1)) / 2

theorem two_mul_associahedronEdgeCount (N : ℕ) :
    2 * associahedronEdgeCount N = (N - 2) * catalan (N - 1) :=
  Nat.mul_div_cancel' (two_dvd_degree_mul_catalan N)

/-- Handshaking identity in `ℕ`: twice the undirected edge count equals the sum of
proper internal span degrees across all trees of `FullBracketing N`. -/
theorem two_mul_associahedronEdgeCount_eq_sum (N : ℕ) (hN : 2 ≤ N) :
    2 * associahedronEdgeCount N = ∑ T : FullBracketing N, (properInternalSpans T).card := by
  rw [two_mul_associahedronEdgeCount, properInternalSpans_total_sum N hN]

private def rootRightNeighbor (l r : BinaryTree Unit) : Finset (BinaryTree Unit) :=
  match l with
  | .nil => ∅
  | .node _ a b => {.node () a (.node () b r)}

private def rootLeftNeighbor (l r : BinaryTree Unit) : Finset (BinaryTree Unit) :=
  match r with
  | .nil => ∅
  | .node _ b c => {.node () (.node () l b) c}

/-- The explicit set of single-rotation neighbors (left or right) of a binary tree. -/
def rotationNeighbors : BinaryTree Unit → Finset (BinaryTree Unit)
  | .nil => ∅
  | .node _ l r =>
    (rotationNeighbors l).image (fun l' => .node () l' r) ∪
      (rotationNeighbors r).image (fun r' => .node () l r') ∪
      rootRightNeighbor l r ∪ rootLeftNeighbor l r

theorem mem_rotationNeighbors_iff (t u : BinaryTree Unit) :
    u ∈ rotationNeighbors t ↔ Nonempty (RotationStep t u) := by
  induction t generalizing u with
  | nil =>
    simp only [rotationNeighbors, Finset.notMem_empty, false_iff]
    rintro ⟨e⟩
    cases e with
    | right h => cases h
    | left h => cases h
  | node val l r il ir =>
    cases val
    simp only [rotationNeighbors, Finset.mem_union, Finset.mem_image]
    constructor
    · intro hu
      rcases hu with ((⟨l', hl', rfl⟩ | ⟨r', hr', rfl⟩) | hrr) | hrl
      · obtain ⟨e⟩ := (il l').mp hl'
        cases e with
        | right h => exact ⟨.right (.left h r)⟩
        | left h => exact ⟨.left (.left h r)⟩
      · obtain ⟨e⟩ := (ir r').mp hr'
        cases e with
        | right h => exact ⟨.right (.right l h)⟩
        | left h => exact ⟨.left (.right l h)⟩
      · cases l with
        | nil => simp [rootRightNeighbor] at hrr
        | node v a b =>
          cases v
          simp only [rootRightNeighbor, Finset.mem_singleton] at hrr
          rw [hrr]
          exact ⟨.right (.root a b r)⟩
      · cases r with
        | nil => simp [rootLeftNeighbor] at hrl
        | node v b c =>
          cases v
          simp only [rootLeftNeighbor, Finset.mem_singleton] at hrl
          rw [hrl]
          exact ⟨.left (.root l b c)⟩
    · rintro ⟨e⟩
      cases e with
      | right h =>
        cases h with
        | root a b c =>
          left; right
          simp [rootRightNeighbor]
        | left h' _ =>
          left; left; left
          exact ⟨_, (il _).mpr ⟨.right h'⟩, rfl⟩
        | right _ h' =>
          left; left; right
          exact ⟨_, (ir _).mpr ⟨.right h'⟩, rfl⟩
      | left h =>
        cases h with
        | root a b c =>
          right
          simp [rootLeftNeighbor]
        | left h' _ =>
          left; left; left
          exact ⟨_, (il _).mpr ⟨.left h'⟩, rfl⟩
        | right _ h' =>
          left; left; right
          exact ⟨_, (ir _).mpr ⟨.left h'⟩, rfl⟩

private theorem rotationNeighbors_numLeaves {t u : BinaryTree Unit}
    (hu : u ∈ rotationNeighbors t) : u.numLeaves = t.numLeaves := by
  obtain ⟨e⟩ := (mem_rotationNeighbors_iff t u).mp hu
  cases e with
  | right h => exact h.numLeaves_eq.symm
  | left h => exact h.numLeaves_eq

theorem rotationNeighbors_card (t : BinaryTree Unit) (ht : 2 ≤ t.numLeaves) :
    (rotationNeighbors t).card = t.numLeaves - 2 := by
  induction t with
  | nil =>
    simp [BinaryTree.numLeaves] at ht
  | node val l r il ir =>
    cases val
    have hl_pos := l.numLeaves_pos
    have hr_pos := r.numLeaves_pos
    dsimp only [rotationNeighbors]
    set fromLeft := (rotationNeighbors l).image (fun l' => BinaryTree.node () l' r)
    set fromRight := (rotationNeighbors r).image (fun r' => BinaryTree.node () l r')
    set rootRight := rootRightNeighbor l r
    set rootLeft := rootLeftNeighbor l r
    have hfl_leaves : ∀ x ∈ fromLeft,
        ∃ l' r', x = BinaryTree.node () l' r' ∧ l'.numLeaves = l.numLeaves := by
      intro x hx
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hx
      exact ⟨l', r, rfl, rotationNeighbors_numLeaves hl'⟩
    have hfr_leaves : ∀ x ∈ fromRight,
        ∃ l' r', x = BinaryTree.node () l' r' ∧ l'.numLeaves = l.numLeaves := by
      intro x hx
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hx
      exact ⟨l, r', rfl, rfl⟩
    have hrr_leaves : ∀ x ∈ rootRight,
        ∃ l' r', x = BinaryTree.node () l' r' ∧ l'.numLeaves < l.numLeaves := by
      intro x hx
      cases l with
      | nil => simp [rootRight, rootRightNeighbor] at hx
      | node _ a b =>
        simp only [rootRight, rootRightNeighbor, Finset.mem_singleton] at hx
        rw [hx]
        have hb := b.numLeaves_pos
        exact ⟨a, .node () b r, rfl, by simp [BinaryTree.numLeaves]; omega⟩
    have hrl_leaves : ∀ x ∈ rootLeft,
        ∃ l' r', x = BinaryTree.node () l' r' ∧ l.numLeaves < l'.numLeaves := by
      intro x hx
      cases r with
      | nil => simp [rootLeft, rootLeftNeighbor] at hx
      | node _ b c =>
        simp only [rootLeft, rootLeftNeighbor, Finset.mem_singleton] at hx
        rw [hx]
        have hb := b.numLeaves_pos
        exact ⟨.node () l b, c, rfl, by simp [BinaryTree.numLeaves]; omega⟩
    have hd1 : Disjoint fromLeft fromRight := by
      apply Finset.disjoint_left.mpr
      intro x h1 h2
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨r', hr', he⟩ := Finset.mem_image.mp h2
      have hle := (BinaryTree.node.inj he).2.1
      have hmem : l ∈ rotationNeighbors l := hle ▸ hl'
      obtain ⟨e⟩ := (mem_rotationNeighbors_iff l l).mp hmem
      cases e with
      | right h =>
        obtain ⟨p, hp, _, hnot⟩ := h.changed_span 0
        exact hnot hp
      | left h =>
        obtain ⟨p, hp, _, hnot⟩ := h.changed_span 0
        exact hnot hp
    have hd2 : Disjoint (fromLeft ∪ fromRight) rootRight := by
      apply Finset.disjoint_left.mpr
      intro x hx hrr
      obtain ⟨l1, r1, hx1, hl1⟩ := hrr_leaves x hrr
      rcases Finset.mem_union.mp hx with h1 | h2
      · obtain ⟨l2, r2, hx2, hl2⟩ := hfl_leaves x h1
        rw [hx1] at hx2
        have he := (BinaryTree.node.inj hx2).2.1
        rw [he] at hl1
        omega
      · obtain ⟨l2, r2, hx2, hl2⟩ := hfr_leaves x h2
        rw [hx1] at hx2
        have he := (BinaryTree.node.inj hx2).2.1
        rw [he] at hl1
        omega
    have hd3 : Disjoint (fromLeft ∪ fromRight ∪ rootRight) rootLeft := by
      apply Finset.disjoint_left.mpr
      intro x hx hrl
      obtain ⟨l1, r1, hx1, hl1⟩ := hrl_leaves x hrl
      rcases Finset.mem_union.mp hx with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · obtain ⟨l2, r2, hx2, hl2⟩ := hfl_leaves x h1
          rw [hx1] at hx2
          have he := (BinaryTree.node.inj hx2).2.1
          rw [he] at hl1
          omega
        · obtain ⟨l2, r2, hx2, hl2⟩ := hfr_leaves x h2
          rw [hx1] at hx2
          have he := (BinaryTree.node.inj hx2).2.1
          rw [he] at hl1
          omega
      · obtain ⟨l2, r2, hx2, hl2⟩ := hrr_leaves x h3
        rw [hx1] at hx2
        have he := (BinaryTree.node.inj hx2).2.1
        rw [he] at hl1
        omega
    rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
      Finset.card_union_of_disjoint hd1]
    have hcard_l : fromLeft.card = (rotationNeighbors l).card :=
      Finset.card_image_of_injective _ (fun a b h => (BinaryTree.node.inj h).2.1)
    have hcard_r : fromRight.card = (rotationNeighbors r).card :=
      Finset.card_image_of_injective _ (fun a b h => (BinaryTree.node.inj h).2.2)
    have hleft_sum : fromLeft.card + rootRight.card = l.numLeaves - 1 := by
      cases l with
      | nil =>
        have h0 : rotationNeighbors .nil = ∅ := rfl
        simp [fromLeft, rootRight, rootRightNeighbor, h0, BinaryTree.numLeaves]
      | node v a b =>
        have h2 : 2 ≤ (BinaryTree.node v a b).numLeaves := by
          have ha := a.numLeaves_pos; have hb := b.numLeaves_pos
          simp [BinaryTree.numLeaves]; omega
        have hil := il h2
        have hrr_card : rootRight.card = 1 := by simp [rootRight, rootRightNeighbor]
        rw [hcard_l, hil, hrr_card]
        omega
    have hright_sum : fromRight.card + rootLeft.card = r.numLeaves - 1 := by
      cases r with
      | nil =>
        have h0 : rotationNeighbors .nil = ∅ := rfl
        simp [fromRight, rootLeft, rootLeftNeighbor, h0, BinaryTree.numLeaves]
      | node v b c =>
        have h2 : 2 ≤ (BinaryTree.node v b c).numLeaves := by
          have hb := b.numLeaves_pos; have hc := c.numLeaves_pos
          simp [BinaryTree.numLeaves]; omega
        have hir := ir h2
        have hrl_card : rootLeft.card = 1 := by simp [rootLeft, rootLeftNeighbor]
        rw [hcard_r, hir, hrl_card]
        omega
    simp only [BinaryTree.numLeaves]
    omega

/-- The Tamari rotation graph on `FullBracketing N` (`1`-skeleton of `K_N`). -/
def tamariGraph (N : ℕ) : SimpleGraph (FullBracketing N) where
  Adj s t := Nonempty (RotationStep s.val t.val)
  symm := ⟨fun _ _ ⟨e⟩ => ⟨e.reverse⟩⟩
  loopless := ⟨fun s ⟨e⟩ => by
    cases e with
    | right h => exact h.fullBracketings_ne s s rfl
    | left h => exact h.fullBracketings_ne s s rfl⟩

noncomputable instance (N : ℕ) : DecidableRel (tamariGraph N).Adj := by
  intro s t
  change Decidable (Nonempty (RotationStep s.val t.val))
  exact decidable_of_iff (t.val ∈ rotationNeighbors s.val) (mem_rotationNeighbors_iff s.val t.val)

/-- Every vertex of `K_N` (`2 ≤ N`) has exact degree `N - 2` in the Tamari rotation graph. -/
theorem tamariGraph_degree (N : ℕ) (hN : 2 ≤ N) (T : FullBracketing N) :
    (tamariGraph N).degree T = N - 2 := by
  classical
  have hmem : ∀ u : FullBracketing N,
      u ∈ (tamariGraph N).neighborFinset T ↔ u.val ∈ rotationNeighbors T.val := by
    intro u
    rw [SimpleGraph.mem_neighborFinset]
    exact (mem_rotationNeighbors_iff T.val u.val).symm
  let f : FullBracketing N ↪ BinaryTree Unit := ⟨Subtype.val, Subtype.val_injective⟩
  have himg : ((tamariGraph N).neighborFinset T).map f = rotationNeighbors T.val := by
    ext x
    simp only [Finset.mem_map, f]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hmem u).mp hu
    · intro hx
      have hxleaves : x.numLeaves = N := (rotationNeighbors_numLeaves hx).trans T.property
      exact ⟨⟨x, hxleaves⟩, (hmem ⟨x, hxleaves⟩).mpr hx, rfl⟩
  have hcard := congrArg Finset.card himg
  rw [Finset.card_map, rotationNeighbors_card T.val (by rw [T.property]; exact hN)] at hcard
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hcard, T.property]

/-- The number of edges of the Tamari rotation graph `tamariGraph N` equals
`associahedronEdgeCount N`. -/
theorem tamariGraph_edgeCount (N : ℕ) (hN : 2 ≤ N) :
    Fintype.card (tamariGraph N).edgeSet = associahedronEdgeCount N := by
  classical
  have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges (tamariGraph N)
  have hdeg : ∑ T : FullBracketing N, (tamariGraph N).degree T =
      (N - 2) * catalan (N - 1) := by
    have hconst : ∀ T : FullBracketing N, (tamariGraph N).degree T = N - 2 :=
      fun T => tamariGraph_degree N hN T
    simp_rw [hconst, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      fullBracketing_card_pos_arity N (by omega), mul_comm]
  rw [hdeg, ← two_mul_associahedronEdgeCount N] at hhand
  have hcard : (tamariGraph N).edgeFinset.card = Fintype.card (tamariGraph N).edgeSet := by
    change (tamariGraph N).edgeSet.toFinset.card = Fintype.card (tamariGraph N).edgeSet
    exact Set.toFinset_card (tamariGraph N).edgeSet
  omega

private theorem local_rotate_left_spans (a b c : BinaryTree Unit) (start : ℕ) :
    (treeSpans (.node () (.node () a b) c) start).erase
      (start, start + a.numLeaves + b.numLeaves) ⊆
      treeSpans (.node () a (.node () b c)) start := by
  intro p hp
  have ha := a.numLeaves_pos; have hb := b.numLeaves_pos; have hc := c.numLeaves_pos
  simp only [treeSpans, BinaryTree.numLeaves, Finset.mem_erase, Finset.mem_insert,
    Finset.mem_union, Nat.add_assoc] at hp ⊢
  rcases hp with ⟨hne, h | h | h⟩
  · left; exact h
  · rcases h with h | h | h
    · exact False.elim (hne h)
    · right; left; exact h
    · right; right; right; left; exact h
  · right; right; right; right; exact h

private theorem local_rotate_left_avoids (a b c : BinaryTree Unit) (start : ℕ) :
    (start, start + a.numLeaves + b.numLeaves) ∉
      treeSpans (.node () a (.node () b c)) start := by
  intro hp
  have hnew : (start + a.numLeaves,
      start + a.numLeaves + b.numLeaves + c.numLeaves) ∈
      treeSpans (.node () a (.node () b c)) start := by
    simp only [treeSpans, BinaryTree.numLeaves, Finset.mem_insert, Finset.mem_union, Nat.add_assoc]
    exact Or.inr (Or.inr (Or.inl trivial))
  have h := treeSpans_compatible (.node () a (.node () b c)) start _ hp _ hnew
  have ha := a.numLeaves_pos; have hb := b.numLeaves_pos; have hc := c.numLeaves_pos
  dsimp [SpanCompatible] at h
  omega

private theorem local_rotate_right_spans (a b c : BinaryTree Unit) (start : ℕ) :
    (treeSpans (.node () a (.node () b c)) start).erase
      (start + a.numLeaves, start + a.numLeaves + b.numLeaves + c.numLeaves) ⊆
      treeSpans (.node () (.node () a b) c) start := by
  intro p hp
  have ha := a.numLeaves_pos; have hb := b.numLeaves_pos; have hc := c.numLeaves_pos
  simp only [treeSpans, BinaryTree.numLeaves, Finset.mem_erase, Finset.mem_insert,
    Finset.mem_union, Nat.add_assoc] at hp ⊢
  rcases hp with ⟨hne, h | h | h⟩
  · left; exact h
  · right; left; right; left; exact h
  · rcases h with h | h | h
    · exact False.elim (hne h)
    · right; left; right; right; exact h
    · right; right; exact h

private theorem local_rotate_right_avoids (a b c : BinaryTree Unit) (start : ℕ) :
    (start + a.numLeaves, start + a.numLeaves + b.numLeaves + c.numLeaves) ∉
      treeSpans (.node () (.node () a b) c) start := by
  intro hp
  have he : (start, start + a.numLeaves + b.numLeaves) ∈
      treeSpans (.node () (.node () a b) c) start := by
    simp only [treeSpans, BinaryTree.numLeaves, Finset.mem_insert, Finset.mem_union, Nat.add_assoc]
    exact Or.inr (Or.inl (Or.inl trivial))
  have h := treeSpans_compatible (.node () (.node () a b) c) start _ hp _ he
  have ha := a.numLeaves_pos; have hb := b.numLeaves_pos; have hc := c.numLeaves_pos
  dsimp [SpanCompatible] at h
  omega

/-- Each proper internal span of `T : FullBracketing N` (`3 ≤ N`) corresponds to an adjacent
tree in `tamariGraph N` sharing a 1-dimensional Loday edge of `LodayPolytope (N - 2)`. -/
theorem properInternalSpan_rotation_edge {n : ℕ} (T : FullBracketing (n + 3))
    {p : BracketSpan} (hp : p ∈ properInternalSpans T) :
    ∃ u : FullBracketing (n + 3), (tamariGraph (n + 3)).Adj T u ∧
      treeProperSpans T ∩ treeProperSpans u = (treeProperSpans T).erase p ∧
      LodayFaceDimension (n + 1) (bracketExposedFace (n + 1)
        (bracketIntersection (treePartialBracketing T) (treePartialBracketing u))) = 1 := by
  have hp' : p ∈ treeProperSpans T := by
    rwa [← properInternalSpans_eq_treeProperSpans (by omega)]
  have hmem : p ∈ treeSpans T.val 0 := (Finset.mem_erase.mp hp').2
  have hne : p ≠ (0, 0 + T.val.numLeaves) := by
    have hne0 := (Finset.mem_erase.mp hp').1
    simpa [T.property] using hne0
  have hrot : ∀ (t : BinaryTree Unit) (start : ℕ) (q : BracketSpan),
      q ∈ treeSpans t start → q ≠ (start, start + t.numLeaves) →
      ∃ u : BinaryTree Unit, Nonempty (RotationStep t u) ∧
        (treeSpans t start).erase q ⊆ treeSpans u start ∧ q ∉ treeSpans u start := by
    intro t
    induction t with
    | nil =>
      intro start q hq
      simp [treeSpans] at hq
    | node val l r il ir =>
      intro start q hq hqn
      cases val
      have hl := l.numLeaves_pos
      have hr := r.numLeaves_pos
      simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hq
      rcases hq with hroot | hq | hq
      · exact False.elim (hqn (by simpa [BinaryTree.numLeaves, Nat.add_assoc] using hroot))
      · by_cases he : q = (start, start + l.numLeaves)
        · cases l with
          | nil =>
            have hv := treeSpans_valid .nil start q hq
            dsimp [SpanValid] at hv; omega
          | node v a b =>
            cases v
            refine ⟨.node () a (.node () b r), ⟨.right (.root a b r)⟩, ?_, ?_⟩
            · simpa only [he, BinaryTree.numLeaves, Nat.add_assoc] using
                local_rotate_left_spans a b r start
            · simpa only [he, BinaryTree.numLeaves, Nat.add_assoc] using
                local_rotate_left_avoids a b r start
        · obtain ⟨l', ⟨el⟩, hsub, hnot⟩ := il start q hq he
          have hln : l'.numLeaves = l.numLeaves := by
            cases el with
            | right h => exact h.numLeaves_eq.symm
            | left h => exact h.numLeaves_eq
          refine ⟨.node () l' r, ?_, ?_, ?_⟩
          · cases el with
            | right h => exact ⟨.right (.left h r)⟩
            | left h => exact ⟨.left (.left h r)⟩
          · intro w hw
            have hw' := Finset.mem_erase.mp hw
            simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hw' ⊢
            rcases hw'.2 with hroot | wmem | wmem
            · left; simpa only [hln] using hroot
            · right; left; exact hsub (Finset.mem_erase.mpr ⟨hw'.1, wmem⟩)
            · right; right; simpa only [hln] using wmem
          · intro hmem'
            simp only [treeSpans, Finset.mem_insert, Finset.mem_union, hln] at hmem'
            rcases hmem' with hroot | hmem' | hmem'
            · exact hqn (by simpa only [BinaryTree.numLeaves, Nat.add_assoc] using hroot)
            · exact hnot hmem'
            · have hv := treeSpans_valid l start q hq
              have hw := treeSpans_valid r (start + l.numLeaves) q hmem'
              dsimp [SpanValid] at *; omega
      · by_cases he : q = (start + l.numLeaves, start + l.numLeaves + r.numLeaves)
        · cases r with
          | nil =>
            have hv := treeSpans_valid .nil (start + l.numLeaves) q hq
            dsimp [SpanValid] at hv; omega
          | node v b c =>
            cases v
            refine ⟨.node () (.node () l b) c, ⟨.left (.root l b c)⟩, ?_, ?_⟩
            · simpa only [he, BinaryTree.numLeaves, Nat.add_assoc] using
                local_rotate_right_spans l b c start
            · simpa only [he, BinaryTree.numLeaves, Nat.add_assoc] using
                local_rotate_right_avoids l b c start
        · obtain ⟨r', ⟨er⟩, hsub, hnot⟩ := ir (start + l.numLeaves) q hq he
          have hrn : r'.numLeaves = r.numLeaves := by
            cases er with
            | right h => exact h.numLeaves_eq.symm
            | left h => exact h.numLeaves_eq
          refine ⟨.node () l r', ?_, ?_, ?_⟩
          · cases er with
            | right h => exact ⟨.right (.right l h)⟩
            | left h => exact ⟨.left (.right l h)⟩
          · intro w hw
            have hw' := Finset.mem_erase.mp hw
            simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hw' ⊢
            rcases hw'.2 with hroot | wmem | wmem
            · left; simpa only [hrn] using hroot
            · right; left; exact wmem
            · right; right; exact hsub (Finset.mem_erase.mpr ⟨hw'.1, wmem⟩)
          · intro hmem'
            simp only [treeSpans, Finset.mem_insert, Finset.mem_union, hrn] at hmem'
            rcases hmem' with hroot | hmem' | hmem'
            · exact hqn (by simpa only [BinaryTree.numLeaves, Nat.add_assoc] using hroot)
            · have hv := treeSpans_valid r (start + l.numLeaves) q hq
              have hw := treeSpans_valid l start q hmem'
              dsimp [SpanValid] at *; omega
            · exact hnot hmem'
  obtain ⟨u', ⟨e⟩, hsub, hnot⟩ := hrot T.val 0 p hmem hne
  have hun : u'.numLeaves = n + 3 := by
    cases e with
    | right h => exact h.numLeaves_eq.symm.trans T.property
    | left h => exact h.numLeaves_eq.trans T.property
  let u : FullBracketing (n + 3) := ⟨u', hun⟩
  refine ⟨u, ⟨e⟩, ?_, ?_⟩
  · have hp_not_u : p ∉ treeProperSpans u := fun hm => hnot (Finset.mem_erase.mp hm).2
    have hsub_proper : (treeProperSpans T).erase p ⊆ treeProperSpans u := by
      intro q hq
      have hq' := Finset.mem_erase.mp hq
      have hqT := Finset.mem_erase.mp hq'.2
      exact Finset.mem_erase.mpr ⟨hqT.1, hsub (Finset.mem_erase.mpr ⟨hq'.1, hqT.2⟩)⟩
    ext q
    constructor
    · intro hq
      obtain ⟨hqT, hqU⟩ := Finset.mem_inter.mp hq
      exact Finset.mem_erase.mpr ⟨fun he => hp_not_u (he ▸ hqU), hqT⟩
    · intro hq
      exact Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hq).2, hsub_proper hq⟩
  · cases e with
    | right h => exact rightRotation_commonFace_dimension (n + 1) T u h
    | left h =>
      have hdim := rightRotation_commonFace_dimension (n + 1) u T h
      have hinter_comm : bracketIntersection (treePartialBracketing T) (treePartialBracketing u) =
          bracketIntersection (treePartialBracketing u) (treePartialBracketing T) := by
        apply Subtype.ext
        exact Finset.inter_comm _ _
      rwa [hinter_comm]

end EdgeRegularityAndDoubleCounting

section ExponentialVsQuadraticGrowth

/-- Upper central binomial bound: `choose (2 * m) m ≤ 4 ^ m`. -/
theorem centralBinom_le_four_pow (m : ℕ) :
    Nat.choose (2 * m) m ≤ 4 ^ m := by
  have hsum : ∑ k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) k = 4 ^ m := by
    rw [Nat.sum_range_choose (2 * m)]
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_mul]
  rw [← hsum]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega))

/-- Lower central binomial bound: `4 ^ m ≤ (2 * m + 1) * choose (2 * m) m`. -/
theorem four_pow_le_mul_centralBinom (m : ℕ) :
    4 ^ m ≤ (2 * m + 1) * Nat.choose (2 * m) m := by
  have hsum : ∑ k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) k = 4 ^ m := by
    rw [Nat.sum_range_choose (2 * m)]
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_mul]
  rw [← hsum]
  calc
    ∑ k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) k
      ≤ ∑ _k ∈ Finset.range (2 * m + 1), Nat.choose (2 * m) m := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hmid := Nat.choose_le_middle k (2 * m)
        simpa [Nat.mul_div_cancel_left m (by decide : 0 < 2)] using hmid
    _ = (2 * m + 1) * Nat.choose (2 * m) m := by
        simp [Finset.sum_const, smul_eq_mul]

theorem catalan_mul_succ_le_four_pow (m : ℕ) :
    (m + 1) * catalan m ≤ 4 ^ m := by
  rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
  exact centralBinom_le_four_pow m

theorem four_pow_le_catalan_mul (m : ℕ) :
    4 ^ m ≤ (2 * m + 1) * (m + 1) * catalan m := by
  rw [mul_assoc, succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
  exact four_pow_le_mul_centralBinom m

theorem associahedronEdgeCount_pos (N : ℕ) (hN : 3 ≤ N) :
    0 < associahedronEdgeCount N := by
  have hcat_pos : 0 < catalan (N - 1) := by
    have hcb : 0 < Nat.centralBinom (N - 1) := Nat.centralBinom_pos (N - 1)
    by_contra h0
    have h0' : catalan (N - 1) = 0 := by omega
    have hmul := succ_mul_catalan_eq_centralBinom (N - 1)
    rw [h0', mul_zero] at hmul
    omega
  have h2E := two_mul_associahedronEdgeCount N
  have hprod : 0 < (N - 2) * catalan (N - 1) := Nat.mul_pos (by omega) hcat_pos
  omega

theorem associahedronEdgeCount_le_four_pow (N : ℕ) (hN : 1 ≤ N) :
    associahedronEdgeCount N ≤ 4 ^ (N - 1) := by
  have h2E := two_mul_associahedronEdgeCount N
  have hcat := catalan_mul_succ_le_four_pow (N - 1)
  rw [Nat.sub_add_cancel hN] at hcat
  have h1 : (N - 2) * catalan (N - 1) ≤ N * catalan (N - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : 2 * associahedronEdgeCount N ≤ 4 ^ (N - 1) := by omega
  omega

theorem four_pow_le_associahedronEdgeCount_mul (N : ℕ) (hN : 1 ≤ N) :
    (N - 2) * 4 ^ (N - 1) ≤ 2 * (2 * N - 1) * N * associahedronEdgeCount N := by
  have hcat := four_pow_le_catalan_mul (N - 1)
  have hsub1 : 2 * (N - 1) + 1 = 2 * N - 1 := by omega
  have hsub2 : N - 1 + 1 = N := by omega
  rw [hsub1, hsub2] at hcat
  have hmul : (N - 2) * 4 ^ (N - 1) ≤
      (N - 2) * ((2 * N - 1) * N * catalan (N - 1)) :=
    Nat.mul_le_mul_left (N - 2) hcat
  have hre : (N - 2) * ((2 * N - 1) * N * catalan (N - 1)) =
      (2 * N - 1) * N * ((N - 2) * catalan (N - 1)) := by ring
  rw [hre, ← two_mul_associahedronEdgeCount N] at hmul
  linarith

private theorem nat_pow_three_div_four_pow_tendsto :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 3 / (4 : ℝ) ^ N) atTop (𝓝 0) := by
  have h4 : ∀ m : ℕ, 4 ≤ m → (m * (m - 1) * (m - 2) * (m - 3) : ℕ) * 81 ≤ 24 * 4 ^ m := by
    intro m hm
    have hbin := add_pow (3 : ℕ) 1 m
    have h4eq : 3 + 1 = 4 := by norm_num
    rw [h4eq] at hbin
    simp only [Nat.cast_id] at hbin
    have hsingle : 3 ^ 4 * 1 ^ (m - 4) * Nat.choose m 4 ≤ 4 ^ m := by
      rw [hbin]
      exact Finset.single_le_sum
        (f := fun x => 3 ^ x * 1 ^ (m - x) * Nat.choose m x)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    simp only [one_pow, mul_one] at hsingle
    have hdesc : Nat.descFactorial m 4 = Nat.factorial 4 * Nat.choose m 4 := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
    have hdesc_eq : Nat.descFactorial m 4 = m * (m - 1) * (m - 2) * (m - 3) := by
      simp [Nat.descFactorial_succ]
      ring
    have h24 : Nat.factorial 4 = 24 := by decide
    have h81 : 3 ^ 4 = 81 := by norm_num
    rw [h81] at hsingle
    rw [hdesc_eq, h24] at hdesc
    nlinarith
  have hbound : ∀ N : ℕ, 8 ≤ N → (N : ℝ) ^ 3 / (4 : ℝ) ^ N ≤ 12 / (N : ℝ) := by
    intro N hN
    have hN4 : 4 ≤ N := by omega
    have hN0 : (0 : ℝ) < (N : ℝ) := by positivity
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ N := by positivity
    have hnat := h4 N hN4
    have hreal : ((N * (N - 1) * (N - 2) * (N - 3) : ℕ) : ℝ) * 81 ≤ 24 * (4 : ℝ) ^ N := by
      exact_mod_cast hnat
    have hsub1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
    have hsub2 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ N)]; norm_num
    have hsub3 : ((N - 3 : ℕ) : ℝ) = (N : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega : 3 ≤ N)]; norm_num
    push_cast at hreal
    rw [hsub1, hsub2, hsub3] at hreal
    have hNR : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlo1 : (N : ℝ) / 2 ≤ (N : ℝ) - 1 := by linarith
    have hlo2 : (N : ℝ) / 2 ≤ (N : ℝ) - 2 := by linarith
    have hlo3 : (N : ℝ) / 2 ≤ (N : ℝ) - 3 := by linarith
    have h12 : (N : ℝ) / 2 * ((N : ℝ) / 2) ≤ ((N : ℝ) - 1) * ((N : ℝ) - 2) := by nlinarith
    have h123 : (N : ℝ) / 2 * ((N : ℝ) / 2) * ((N : ℝ) / 2) ≤
        ((N : ℝ) - 1) * ((N : ℝ) - 2) * ((N : ℝ) - 3) := by
      exact mul_le_mul h12 hlo3 (by positivity) (by nlinarith)
    have hprod : (N : ℝ) ^ 4 / 8 ≤ (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) * ((N : ℝ) - 3) := by
      have hmulN := mul_le_mul_of_nonneg_left h123 (le_of_lt hN0)
      linarith
    have hpow4 : (N : ℝ) ^ 4 * 81 / 8 ≤ 24 * (4 : ℝ) ^ N := by linarith
    rw [div_le_div_iff₀ h4pos hN0]
    nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_const_nhds (x := (12 : ℝ))).div_atTop tendsto_natCast_atTop_atTop) ?_ ?_
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_ge_atTop 8] with N hN
    exact hbound N hN

private theorem real_log_nat_div_tendsto :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hlog : ∀ x : ℝ, 1 ≤ x → Real.log x ≤ 2 * Real.sqrt x := by
    intro x hx
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have hle : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      calc
        Real.log x = Real.log (Real.sqrt x ^ 2) := by rw [hsq]
        _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; norm_num
    linarith
  have hdiv : Tendsto (fun N : ℕ => 2 / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop hsqrt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact div_nonneg (Real.log_nonneg h1) (by linarith)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hs0 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
    have hle := hlog (N : ℝ) h1
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt (by linarith)
    rw [div_le_div_iff₀ hN0 hs0]
    nlinarith

/-- **Exponential Edge Growth:**
`log (associahedronEdgeCount N) / ((N - 1) * log 4) → 1` as `N → ∞`. -/
theorem log_edgeCount_div_tendsto :
    Tendsto
      (fun N : ℕ => Real.log (associahedronEdgeCount N) / (((N : ℝ) - 1) * Real.log 4))
      atTop (𝓝 1) := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlo : Tendsto
      (fun N : ℕ => 1 - Real.log (8 * (N : ℝ)) / (((N : ℝ) - 1) * Real.log 4))
      atTop (𝓝 1) := by
    have hnum : Tendsto (fun N : ℕ => Real.log (8 * (N : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
      have heq : Tendsto (fun N : ℕ =>
          Real.log 8 / (N : ℝ) + Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 (0 + 0)) :=
        ((tendsto_const_nhds (x := Real.log 8)).div_atTop tendsto_natCast_atTop_atTop).add
          real_log_nat_div_tendsto
      rw [add_zero] at heq
      refine heq.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      rw [Real.log_mul (by norm_num) hN0, add_div]
    have hden : Tendsto (fun N : ℕ => (N : ℝ) / (((N : ℝ) - 1) * Real.log 4))
        atTop (𝓝 (1 / Real.log 4)) := by
      have hsub : Tendsto (fun N : ℕ => (1 : ℝ) - 1 / (N : ℝ)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub
          ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_natCast_atTop_atTop)
      rw [sub_zero] at hsub
      have hdiv := (tendsto_const_nhds (x := (1 : ℝ))).div (hsub.mul tendsto_const_nhds)
        (ne_of_gt (by linarith))
      have hlim : (1 : ℝ) / (1 * Real.log 4) = 1 / Real.log 4 := by ring
      rw [hlim] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      have hN1 : (N : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      dsimp
      field_simp [hN0, hN1]
    have hprod := hnum.mul hden
    rw [zero_mul] at hprod
    have hsub := tendsto_const_nhds (x := (1 : ℝ)).sub hprod
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    field_simp [hN0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 4] with N hN
    have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hden_pos : 0 < ((N : ℝ) - 1) * Real.log 4 := mul_pos hN1 hlog4
    have hEpos : (0 : ℝ) < (associahedronEdgeCount N : ℝ) := by
      exact_mod_cast associahedronEdgeCount_pos N (by omega)
    have hnat := four_pow_le_associahedronEdgeCount_mul N (by omega)
    have hreal : ((N - 2 : ℕ) : ℝ) * (4 : ℝ) ^ (N - 1) ≤
        2 * ((2 * N - 1 : ℕ) : ℝ) * (N : ℝ) * (associahedronEdgeCount N : ℝ) := by
      exact_mod_cast hnat
    have hN2 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ N)]; norm_num
    have h2N1 : ((2 * N - 1 : ℕ) : ℝ) = 2 * (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * N)]; push_cast; norm_num
    rw [hN2, h2N1] at hreal
    have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hsimple : (4 : ℝ) ^ (N - 1) ≤ 8 * (N : ℝ) * (associahedronEdgeCount N : ℝ) := by
      have h1 : (N : ℝ) / 2 * (4 : ℝ) ^ (N - 1) ≤ ((N : ℝ) - 2) * (4 : ℝ) ^ (N - 1) := by
        have h4p : 0 ≤ (4 : ℝ) ^ (N - 1) := by positivity
        nlinarith
      have h2 : 2 * (2 * (N : ℝ) - 1) * (N : ℝ) ≤ 4 * (N : ℝ) * (N : ℝ) := by nlinarith
      have h3 : 2 * (2 * (N : ℝ) - 1) * (N : ℝ) * (associahedronEdgeCount N : ℝ) ≤
          4 * (N : ℝ) * (N : ℝ) * (associahedronEdgeCount N : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt hEpos)
      have h4 : (N : ℝ) / 2 * (4 : ℝ) ^ (N - 1) ≤
          4 * (N : ℝ) * (N : ℝ) * (associahedronEdgeCount N : ℝ) := by linarith
      nlinarith
    have hlog_ineq : (N - 1 : ℕ) * Real.log 4 ≤
        Real.log (8 * (N : ℝ)) + Real.log (associahedronEdgeCount N : ℝ) := by
      have h1 : Real.log ((4 : ℝ) ^ (N - 1)) ≤
          Real.log (8 * (N : ℝ) * (associahedronEdgeCount N : ℝ)) :=
        Real.log_le_log (by positivity) hsimple
      rw [Real.log_pow, Real.log_mul (by positivity) (ne_of_gt hEpos)] at h1
      exact h1
    have hNm1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
    rw [hNm1] at hlog_ineq
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hden_pos]
    linarith
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hden_pos : 0 < ((N : ℝ) - 1) * Real.log 4 := mul_pos hN1 hlog4
    have hEpos : (0 : ℝ) < (associahedronEdgeCount N : ℝ) := by
      exact_mod_cast associahedronEdgeCount_pos N hN
    have hle : (associahedronEdgeCount N : ℝ) ≤ (4 : ℝ) ^ (N - 1) := by
      exact_mod_cast associahedronEdgeCount_le_four_pow N (by omega)
    have hlog_le := Real.log_le_log hEpos hle
    rw [Real.log_pow] at hlog_le
    have hNm1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
    rw [hNm1] at hlog_le
    exact (div_le_one hden_pos).mpr hlog_le

/-- Tamari left-edge potential: sum over all internal nodes of `(l.numLeaves - 1)`.
Strictly decreases by at least `1` on every `RightRotation`, giving antisymmetry and the
exact quadratic height bound `(N - 1) * (N - 2) / 2`. -/
def leftEdgeCount : BinaryTree Unit → ℕ
  | .nil => 0
  | .node _ l r => (l.numLeaves - 1) + leftEdgeCount l + leftEdgeCount r

theorem RightRotation.leftEdgeCount_lt {s t : BracketTree} (h : RightRotation s t) :
    leftEdgeCount t + 1 ≤ leftEdgeCount s := by
  induction h with
  | root a b c =>
    have ha := a.numLeaves_pos
    have hb := b.numLeaves_pos
    simp only [leftEdgeCount, BinaryTree.numLeaves]
    omega
  | left h u ih =>
    have hlen := h.numLeaves_eq
    simp only [leftEdgeCount, hlen]
    omega
  | right u h ih =>
    simp only [leftEdgeCount]
    omega

private theorem leftEdgeCount_le_aux (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 * (a - 1) + (a - 1) * (a - 2) + (b - 1) * (b - 2) ≤ (a + b - 1) * (a + b - 2) := by
  cases a with
  | zero => omega
  | succ a' =>
    cases b with
    | zero => omega
    | succ b' =>
      cases a' with
      | zero =>
        cases b' with
        | zero => simp
        | succ b'' =>
          have h0 : 0 + 1 - 1 = 0 := rfl
          have h1 : 1 + (b'' + 1 + 1) - 1 = b'' + 2 := by omega
          have h2 : 1 + (b'' + 1 + 1) - 2 = b'' + 1 := by omega
          have h3 : b'' + 1 + 1 - 1 = b'' + 1 := by omega
          have h4 : b'' + 1 + 1 - 2 = b'' := by omega
          rw [h0, h1, h2, h3, h4]
          nlinarith
      | succ a'' =>
        cases b' with
        | zero =>
          have h0 : 0 + 1 - 1 = 0 := rfl
          have h1 : a'' + 1 + 1 - 1 = a'' + 1 := by omega
          have h2 : a'' + 1 + 1 - 2 = a'' := by omega
          have h3 : a'' + 1 + 1 + 1 - 1 = a'' + 2 := by omega
          have h4 : a'' + 1 + 1 + 1 - 2 = a'' + 1 := by omega
          rw [h0, h1, h2, h3, h4]
          nlinarith
        | succ b'' =>
          have h1 : a'' + 1 + 1 - 1 = a'' + 1 := by omega
          have h2 : a'' + 1 + 1 - 2 = a'' := by omega
          have h3 : b'' + 1 + 1 - 1 = b'' + 1 := by omega
          have h4 : b'' + 1 + 1 - 2 = b'' := by omega
          have h5 : a'' + 1 + 1 + (b'' + 1 + 1) - 1 = a'' + b'' + 3 := by omega
          have h6 : a'' + 1 + 1 + (b'' + 1 + 1) - 2 = a'' + b'' + 2 := by omega
          rw [h1, h2, h3, h4, h5, h6]
          nlinarith

theorem leftEdgeCount_le (t : BinaryTree Unit) :
    leftEdgeCount t ≤ (t.numLeaves - 1) * (t.numLeaves - 2) / 2 := by
  induction t with
  | nil => simp [leftEdgeCount, BinaryTree.numLeaves]
  | node _ l r il ir =>
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    have hil : 2 * leftEdgeCount l ≤ (l.numLeaves - 1) * (l.numLeaves - 2) :=
      (Nat.mul_le_mul_left 2 il).trans (Nat.mul_div_le _ 2)
    have hir : 2 * leftEdgeCount r ≤ (r.numLeaves - 1) * (r.numLeaves - 2) :=
      (Nat.mul_le_mul_left 2 ir).trans (Nat.mul_div_le _ 2)
    have haux := leftEdgeCount_le_aux l.numLeaves r.numLeaves hl hr
    have h2 : 2 * leftEdgeCount (BinaryTree.node () l r) ≤
        ((BinaryTree.node () l r).numLeaves - 1) *
          ((BinaryTree.node () l r).numLeaves - 2) := by
      simp only [leftEdgeCount, BinaryTree.numLeaves]
      omega
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by linarith)

theorem leftEdgeCount_le_choose_two (t : BinaryTree Unit) :
    leftEdgeCount t ≤ t.numLeaves * (t.numLeaves - 1) / 2 := by
  refine (leftEdgeCount_le t).trans (Nat.div_le_div_right ?_)
  exact Nat.mul_le_mul (by omega) (by omega)

/-- General Tamari order on `FullBracketing N`: reflexive-transitive closure of `RightRotation`. -/
def TamariLE {N : ℕ} (s t : FullBracketing N) : Prop :=
  Relation.ReflTransGen RightRotation s.val t.val

private theorem reflTransGen_rightRotation_leftEdgeCount_le {u v : BracketTree}
    (h : Relation.ReflTransGen RightRotation u v) :
    leftEdgeCount v ≤ leftEdgeCount u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    have hlt := hstep.leftEdgeCount_lt
    omega

theorem tamariLE_leftEdgeCount_le {N : ℕ} {s t : FullBracketing N} (h : TamariLE s t) :
    leftEdgeCount t.val ≤ leftEdgeCount s.val :=
  reflTransGen_rightRotation_leftEdgeCount_le h

theorem tamariLE_refl {N : ℕ} (s : FullBracketing N) : TamariLE s s :=
  Relation.ReflTransGen.refl

theorem tamariLE_trans {N : ℕ} {a b c : FullBracketing N}
    (hab : TamariLE a b) (hbc : TamariLE b c) : TamariLE a c :=
  hab.trans hbc

theorem tamariLE_antisymm {N : ℕ} {a b : FullBracketing N}
    (hab : TamariLE a b) (hba : TamariLE b a) : a = b := by
  rcases Relation.ReflTransGen.cases_head hab with heq | ⟨c, hac, hcb⟩
  · exact Subtype.ext heq
  · have h1 := hac.leftEdgeCount_lt
    have h2 := reflTransGen_rightRotation_leftEdgeCount_le hcb
    have h3 := tamariLE_leftEdgeCount_le hba
    omega

/-- The Tamari partial order on `FullBracketing N` for every `N : ℕ`. -/
@[instance_reducible]
def tamariPartialOrder (N : ℕ) : PartialOrder (FullBracketing N) where
  le := TamariLE
  le_refl := tamariLE_refl
  le_trans _ _ _ := tamariLE_trans
  le_antisymm _ _ := tamariLE_antisymm

/-- Strict Tamari order relation on `FullBracketing N`. -/
def TamariLT {N : ℕ} (s t : FullBracketing N) : Prop :=
  TamariLE s t ∧ s ≠ t

theorem tamariLT_leftEdgeCount_lt {N : ℕ} {s t : FullBracketing N} (h : TamariLT s t) :
    leftEdgeCount t.val + 1 ≤ leftEdgeCount s.val := by
  rcases h with ⟨hle, hne⟩
  rcases Relation.ReflTransGen.cases_head hle with heq | ⟨c, hsc, hct⟩
  · exact False.elim (hne (Subtype.ext heq))
  · have h1 := hsc.leftEdgeCount_lt
    have h2 := reflTransGen_rightRotation_leftEdgeCount_le hct
    omega

/-- **Quadratic Tamari Height Bound:**
Every strictly increasing chain `c : Fin (L + 1) → FullBracketing N` in the Tamari poset
has length `L ≤ (N - 1) * (N - 2) / 2 ≤ N * (N - 1) / 2`. -/
theorem tamari_chain_length_le {N L : ℕ} (c : Fin (L + 1) → FullBracketing N)
    (hc : ∀ i : Fin L, TamariLT (c i.castSucc) (c i.succ)) :
    L ≤ (N - 1) * (N - 2) / 2 ∧ L ≤ N * (N - 1) / 2 := by
  have hdrop : ∀ k : ℕ, (hk : k ≤ L) →
      leftEdgeCount (c ⟨k, by omega⟩).val + k ≤ leftEdgeCount (c ⟨0, by omega⟩).val := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hstep := tamariLT_leftEdgeCount_lt (hc ⟨k, by omega⟩)
      have he1 : (⟨k, by omega⟩ : Fin L).castSucc = ⟨k, by omega⟩ := rfl
      have he2 : (⟨k, by omega⟩ : Fin L).succ = ⟨k + 1, by omega⟩ := rfl
      rw [he1, he2] at hstep
      omega
  have hL := hdrop L le_rfl
  have hle1 := leftEdgeCount_le (c ⟨0, by omega⟩).val
  have hle2 := leftEdgeCount_le_choose_two (c ⟨0, by omega⟩).val
  rw [(c ⟨0, by omega⟩).property] at hle1 hle2
  omega

/-- **Quadratic Height vs. Exponential Edge Count:**
`(N * (N - 1) / 2 : ℝ) / associahedronEdgeCount N → 0` as `N → ∞`. -/
theorem quadratic_height_div_edgeCount_tendsto :
    Tendsto
      (fun N : ℕ => ((N * (N - 1) / 2 : ℕ) : ℝ) / (associahedronEdgeCount N : ℝ))
      atTop (𝓝 0) := by
  have htop : Tendsto (fun N : ℕ => 16 * ((N : ℝ) ^ 3 / (4 : ℝ) ^ N)) atTop (𝓝 0) := by
    have h := tendsto_const_nhds (x := (16 : ℝ)).mul nat_pow_three_div_four_pow_tendsto
    simpa only [mul_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop ?_ ?_
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_ge_atTop 4] with N hN
    have hEpos : (0 : ℝ) < (associahedronEdgeCount N : ℝ) := by
      exact_mod_cast associahedronEdgeCount_pos N (by omega)
    have hnat := four_pow_le_associahedronEdgeCount_mul N (by omega)
    have hreal : ((N - 2 : ℕ) : ℝ) * (4 : ℝ) ^ (N - 1) ≤
        2 * ((2 * N - 1 : ℕ) : ℝ) * (N : ℝ) * (associahedronEdgeCount N : ℝ) := by
      exact_mod_cast hnat
    have hN2 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ N)]; norm_num
    have h2N1 : ((2 * N - 1 : ℕ) : ℝ) = 2 * (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * N)]; push_cast; norm_num
    rw [hN2, h2N1] at hreal
    have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hsimple : (4 : ℝ) ^ (N - 1) ≤ 8 * (N : ℝ) * (associahedronEdgeCount N : ℝ) := by
      have h1 : (N : ℝ) / 2 * (4 : ℝ) ^ (N - 1) ≤ ((N : ℝ) - 2) * (4 : ℝ) ^ (N - 1) := by
        have h4p : 0 ≤ (4 : ℝ) ^ (N - 1) := by positivity
        nlinarith
      have h2 : 2 * (2 * (N : ℝ) - 1) * (N : ℝ) ≤ 4 * (N : ℝ) * (N : ℝ) := by nlinarith
      have h3 : 2 * (2 * (N : ℝ) - 1) * (N : ℝ) * (associahedronEdgeCount N : ℝ) ≤
          4 * (N : ℝ) * (N : ℝ) * (associahedronEdgeCount N : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt hEpos)
      have h4 : (N : ℝ) / 2 * (4 : ℝ) ^ (N - 1) ≤
          4 * (N : ℝ) * (N : ℝ) * (associahedronEdgeCount N : ℝ) := by linarith
      nlinarith
    have h4N : (4 : ℝ) ^ N = 4 * (4 : ℝ) ^ (N - 1) := by
      have hsub : N = (N - 1) + 1 := by omega
      conv_lhs => rw [hsub, pow_succ]
      ring
    have hq : ((N * (N - 1) / 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 / 2 := by
      have hnatq : 2 * (N * (N - 1) / 2) ≤ N * (N - 1) := Nat.mul_div_le _ 2
      have hrealq : 2 * ((N * (N - 1) / 2 : ℕ) : ℝ) ≤ (N : ℝ) * ((N - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnatq
      have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
      rw [hN1] at hrealq
      nlinarith
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ N := by positivity
    rw [div_le_iff₀ hEpos]
    calc
      ((N * (N - 1) / 2 : ℕ) : ℝ)
        ≤ (N : ℝ) ^ 2 / 2 := hq
      _ ≤ 16 * ((N : ℝ) ^ 3 / (4 : ℝ) ^ N) * (associahedronEdgeCount N : ℝ) := by
        have hmul : (4 : ℝ) ^ N ≤ 32 * (N : ℝ) * (associahedronEdgeCount N : ℝ) := by linarith
        have hdiv : (1 : ℝ) ≤ 32 * (N : ℝ) * (associahedronEdgeCount N : ℝ) / (4 : ℝ) ^ N := by
          rw [le_div_iff₀ h4pos]
          linarith
        have hstep : (N : ℝ) ^ 2 / 2 * 1 ≤
            (N : ℝ) ^ 2 / 2 * (32 * (N : ℝ) * (associahedronEdgeCount N : ℝ) / (4 : ℝ) ^ N) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
        have heq : (N : ℝ) ^ 2 / 2 * (32 * (N : ℝ) * (associahedronEdgeCount N : ℝ) / (4 : ℝ) ^ N) =
            16 * ((N : ℝ) ^ 3 / (4 : ℝ) ^ N) * (associahedronEdgeCount N : ℝ) := by
          ring
        linarith

end ExponentialVsQuadraticGrowth

end FunctorialGeometry
