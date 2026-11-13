/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under the license described in the file LICENSE.
Authors: Shivansh Singh
-/
import MathProject.AssociahedralFacetProducts
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
# Combinatorial theory of sub-associahedral embeddings

This module formalizes the results of `supplymentarylatticenotes.md`:

1. **Sub-Tree Support & Facet Incidence (§1):** Contiguous intervals `[i, i + k)` of arity
   `k` (`2 ≤ k ≤ N`) supported by an internal node of `T ∈ FullBracketing N`, together with
   the proper-interval bridge to `PartialBracketing N` (`2 ≤ k ≤ N - 1`).
2. **Operadic Factorization (§2, Theorem 2.1):** An explicit constructive equivalence
   between `FullBracketing (N - k + 1) × FullBracketing k` and
   `{ T : FullBracketing N // SubtreeSupport T i k }` via leaf grafting, proving the fiber
   cardinality `C_{k-1} * C_{N-k}`.
3. **Global Embedding Sum (§3, Theorem 3.1):** Double counting across intervals and trees,
   yielding `Φ(N, k) = C_{k-1} * choose (2 * (N - k)) (N - k)`.
4. **Minimal Binary Generators (§4, Corollary 4.1):** For `k = 2`,
   `Φ(N, 2) = choose (2 * N - 4) (N - 2)`.
5. **Expected Density & Asymptotics (§5, Theorems 5.1–5.2):** Exact formula for `E[n_k](N)`
   and its linear asymptotic law
   `E[n_k](N) = (C_{k-1} / 4^(k-1)) * N + C_{k-1} * (k - 1) / (2 * 4^(k-1)) + O(1/N)`
   `= (C_{k-1} / 4^(k-1)) * N + O(1)`.
-/

namespace FunctorialGeometry

open Filter Topology Asymptotics

section Grafting

/-- Graft `t_in` at the `j`-th leaf (0-indexed) of `t_out`. -/
def graftTree : BinaryTree Unit → ℕ → BinaryTree Unit → BinaryTree Unit
  | .nil, _, t_in => t_in
  | .node _ l r, j, t_in =>
    if j < l.numLeaves then
      .node () (graftTree l j t_in) r
    else
      .node () l (graftTree r (j - l.numLeaves) t_in)

theorem graftTree_numLeaves (t_out t_in : BinaryTree Unit) (j : ℕ) (hj : j < t_out.numLeaves) :
    (graftTree t_out j t_in).numLeaves = t_out.numLeaves - 1 + t_in.numLeaves := by
  induction t_out generalizing j with
  | nil =>
    simp only [graftTree, BinaryTree.numLeaves] at hj ⊢
    omega
  | node _ l r il ir =>
    simp only [BinaryTree.numLeaves] at hj
    dsimp [graftTree]
    split_ifs with h
    · have hl := l.numLeaves_pos
      have ih := il j h
      simp only [BinaryTree.numLeaves, ih]
      omega
    · have hl := l.numLeaves_pos
      have hr := r.numLeaves_pos
      have ih := ir (j - l.numLeaves) (by omega)
      simp only [BinaryTree.numLeaves, ih]
      omega

/-- Extract the internal subtree spanning `[i, i + k)` inside `t` (starting at leaf `start`). -/
def extractAt : BinaryTree Unit → ℕ → ℕ → ℕ → BinaryTree Unit
  | .nil, _, _, _ => .nil
  | .node _ l r, start, i, k =>
    if i = start ∧ i + k = start + l.numLeaves + r.numLeaves then
      .node () l r
    else if i + k ≤ start + l.numLeaves then
      extractAt l start i k
    else
      extractAt r (start + l.numLeaves) i k

/-- Contract the internal subtree spanning `[i, i + k)` inside `t` to a single leaf. -/
def contractAt : BinaryTree Unit → ℕ → ℕ → ℕ → BinaryTree Unit
  | .nil, _, _, _ => .nil
  | .node _ l r, start, i, k =>
    if i = start ∧ i + k = start + l.numLeaves + r.numLeaves then
      .nil
    else if i + k ≤ start + l.numLeaves then
      .node () (contractAt l start i k) r
    else
      .node () l (contractAt r (start + l.numLeaves) i k)

theorem graftTree_mem_treeSpans (t_out t_in : BinaryTree Unit) (start j : ℕ)
    (hj : j < t_out.numLeaves) (hk : 2 ≤ t_in.numLeaves) :
    (start + j, start + j + t_in.numLeaves) ∈ treeSpans (graftTree t_out j t_in) start := by
  induction t_out generalizing start j with
  | nil =>
    have hj0 : j = 0 := by simp only [BinaryTree.numLeaves] at hj; omega
    subst hj0
    simpa only [graftTree, Nat.add_zero] using treeSpans_root start hk
  | node _ l r il ir =>
    simp only [BinaryTree.numLeaves] at hj
    dsimp [graftTree]
    split_ifs with h
    · simp only [treeSpans, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inl (il start j h))
    · simp only [treeSpans, Finset.mem_insert, Finset.mem_union]
      have hir := ir (start + l.numLeaves) (j - l.numLeaves) (by omega)
      have ha1 : start + l.numLeaves + (j - l.numLeaves) = start + j := by omega
      rw [ha1] at hir
      exact Or.inr (Or.inr hir)

theorem extractAt_numLeaves (t : BinaryTree Unit) (start i k : ℕ)
    (hk : 2 ≤ k) (hmem : (i, i + k) ∈ treeSpans t start) :
    (extractAt t start i k).numLeaves = k := by
  induction t generalizing start with
  | nil => simp [treeSpans] at hmem
  | node _ l r il ir =>
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hmem
    dsimp [extractAt]
    rcases hmem with hroot | hlmem | hrmem
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hroot
      rw [if_pos ⟨h1, h2⟩]
      simp only [BinaryTree.numLeaves]
      omega
    · have hv := treeSpans_valid l start _ hlmem
      dsimp [SpanValid] at hv
      have hnroot : ¬ (i = start ∧ i + k = start + l.numLeaves + r.numLeaves) := by omega
      rw [if_neg hnroot, if_pos hv.2.2]
      exact il start hlmem
    · have hv := treeSpans_valid r (start + l.numLeaves) _ hrmem
      dsimp [SpanValid] at hv
      have hnroot : ¬ (i = start ∧ i + k = start + l.numLeaves + r.numLeaves) := by omega
      have hnleft : ¬ (i + k ≤ start + l.numLeaves) := by omega
      rw [if_neg hnroot, if_neg hnleft]
      exact ir (start + l.numLeaves) hrmem

theorem contractAt_numLeaves (t : BinaryTree Unit) (start i k : ℕ)
    (hk : 2 ≤ k) (hmem : (i, i + k) ∈ treeSpans t start) :
    (contractAt t start i k).numLeaves = t.numLeaves - k + 1 := by
  induction t generalizing start with
  | nil => simp [treeSpans] at hmem
  | node _ l r il ir =>
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hmem
    dsimp [contractAt]
    rcases hmem with hroot | hlmem | hrmem
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hroot
      rw [if_pos ⟨h1, h2⟩]
      simp only [BinaryTree.numLeaves]
      omega
    · have hv := treeSpans_valid l start _ hlmem
      dsimp [SpanValid] at hv
      have hnroot : ¬ (i = start ∧ i + k = start + l.numLeaves + r.numLeaves) := by omega
      rw [if_neg hnroot, if_pos hv.2.2]
      have ih := il start hlmem
      simp only [BinaryTree.numLeaves] at ih ⊢
      omega
    · have hv := treeSpans_valid r (start + l.numLeaves) _ hrmem
      dsimp [SpanValid] at hv
      have hnroot : ¬ (i = start ∧ i + k = start + l.numLeaves + r.numLeaves) := by omega
      have hnleft : ¬ (i + k ≤ start + l.numLeaves) := by omega
      rw [if_neg hnroot, if_neg hnleft]
      have ih := ir (start + l.numLeaves) hrmem
      simp only [BinaryTree.numLeaves] at ih ⊢
      omega

theorem graftTree_contractAt_extractAt (t : BinaryTree Unit) (start i k : ℕ)
    (hk : 2 ≤ k) (hmem : (i, i + k) ∈ treeSpans t start) :
    graftTree (contractAt t start i k) (i - start) (extractAt t start i k) = t := by
  induction t generalizing start with
  | nil => simp [treeSpans] at hmem
  | node val l r il ir =>
    cases val
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    simp only [treeSpans, Finset.mem_insert, Finset.mem_union] at hmem
    dsimp [contractAt, extractAt]
    rcases hmem with hroot | hlmem | hrmem
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hroot
      rw [if_pos ⟨h1, h2⟩, if_pos ⟨h1, h2⟩]
      rfl
    · have hv := treeSpans_valid l start _ hlmem
      dsimp [SpanValid] at hv
      have hnroot : ¬ (i = start ∧ i + k = start + l.numLeaves + r.numLeaves) := by omega
      rw [if_neg hnroot, if_pos hv.2.2, if_neg hnroot, if_pos hv.2.2]
      dsimp [graftTree]
      have hc := contractAt_numLeaves l start i k hk hlmem
      rw [if_pos (by omega)]
      rw [il start hlmem]
    · have hv := treeSpans_valid r (start + l.numLeaves) _ hrmem
      dsimp [SpanValid] at hv
      have hnroot : ¬ (i = start ∧ i + k = start + l.numLeaves + r.numLeaves) := by omega
      have hnleft : ¬ (i + k ≤ start + l.numLeaves) := by omega
      rw [if_neg hnroot, if_neg hnleft, if_neg hnroot, if_neg hnleft]
      dsimp [graftTree]
      rw [if_neg (by omega)]
      have hsub : i - start - l.numLeaves = i - (start + l.numLeaves) := by omega
      rw [hsub, ir (start + l.numLeaves) hrmem]

theorem contractAt_graftTree (t_out t_in : BinaryTree Unit) (start j : ℕ)
    (hj : j < t_out.numLeaves) (hk : 2 ≤ t_in.numLeaves) :
    contractAt (graftTree t_out j t_in) start (start + j) t_in.numLeaves = t_out := by
  induction t_out generalizing start j with
  | nil =>
    have hj0 : j = 0 := by simp only [BinaryTree.numLeaves] at hj; omega
    subst hj0
    cases t_in with
    | nil => simp only [BinaryTree.numLeaves] at hk; omega
    | node val l r =>
      cases val
      simp only [graftTree, contractAt, BinaryTree.numLeaves]
      rw [if_pos (by omega)]
  | node val l r il ir =>
    cases val
    simp only [BinaryTree.numLeaves] at hj
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    dsimp [graftTree]
    split_ifs with h
    · have hgl := graftTree_numLeaves l t_in j h
      dsimp [contractAt]
      have hnroot : ¬ (start + j = start ∧
          start + j + t_in.numLeaves =
            start + (graftTree l j t_in).numLeaves + r.numLeaves) := by
        omega
      rw [if_neg hnroot, if_pos (by omega)]
      rw [il start j h]
    · have hgr := graftTree_numLeaves r t_in (j - l.numLeaves) (by omega)
      dsimp [contractAt]
      have hnroot : ¬ (start + j = start ∧
          start + j + t_in.numLeaves =
            start + l.numLeaves + (graftTree r (j - l.numLeaves) t_in).numLeaves) := by
        omega
      have hnleft : ¬ (start + j + t_in.numLeaves ≤ start + l.numLeaves) := by omega
      rw [if_neg hnroot, if_neg hnleft]
      have hir := ir (start + l.numLeaves) (j - l.numLeaves) (by omega)
      have ha : start + l.numLeaves + (j - l.numLeaves) = start + j := by omega
      rw [ha] at hir
      rw [hir]

theorem extractAt_graftTree (t_out t_in : BinaryTree Unit) (start j : ℕ)
    (hj : j < t_out.numLeaves) (hk : 2 ≤ t_in.numLeaves) :
    extractAt (graftTree t_out j t_in) start (start + j) t_in.numLeaves = t_in := by
  induction t_out generalizing start j with
  | nil =>
    have hj0 : j = 0 := by simp only [BinaryTree.numLeaves] at hj; omega
    subst hj0
    cases t_in with
    | nil => simp only [BinaryTree.numLeaves] at hk; omega
    | node val l r =>
      cases val
      simp only [graftTree, extractAt, BinaryTree.numLeaves]
      rw [if_pos (by omega)]
  | node val l r il ir =>
    cases val
    simp only [BinaryTree.numLeaves] at hj
    have hl := l.numLeaves_pos
    have hr := r.numLeaves_pos
    dsimp [graftTree]
    split_ifs with h
    · have hgl := graftTree_numLeaves l t_in j h
      dsimp [extractAt]
      have hnroot : ¬ (start + j = start ∧
          start + j + t_in.numLeaves =
            start + (graftTree l j t_in).numLeaves + r.numLeaves) := by
        omega
      rw [if_neg hnroot, if_pos (by omega)]
      exact il start j h
    · have hgr := graftTree_numLeaves r t_in (j - l.numLeaves) (by omega)
      dsimp [extractAt]
      have hnroot : ¬ (start + j = start ∧
          start + j + t_in.numLeaves =
            start + l.numLeaves + (graftTree r (j - l.numLeaves) t_in).numLeaves) := by
        omega
      have hnleft : ¬ (start + j + t_in.numLeaves ≤ start + l.numLeaves) := by omega
      rw [if_neg hnroot, if_neg hnleft]
      have hir := ir (start + l.numLeaves) (j - l.numLeaves) (by omega)
      have ha : start + l.numLeaves + (j - l.numLeaves) = start + j := by omega
      rw [ha] at hir
      exact hir

end Grafting

section SupportAndFactorization

/-- Uniform `Fintype` instance on `FullBracketing n` for every `n : ℕ`. -/
@[instance_reducible]
private def instFintypeFullBracketingAll : (n : ℕ) → Fintype (FullBracketing n)
  | 0 => @Fintype.ofIsEmpty _ ⟨no_nullary_fullBracketing⟩
  | _ + 1 => inferInstance

attribute [local instance] instFintypeFullBracketingAll

private theorem fullBracketing_card_of_pos (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (FullBracketing n) = catalan (n - 1) := by
  cases n with
  | zero => omega
  | succ m =>
    rw [Nat.add_sub_cancel]
    convert fullBracketing_card m using 1

/-- Contiguous interval `[i, i + k)` forms a complete sub-tree component in `T`. -/
def SubtreeSupport {N : ℕ} (T : FullBracketing N) (i k : ℕ) : Prop :=
  (i, i + k) ∈ treeSpans T.val 0

instance {N : ℕ} (T : FullBracketing N) (i k : ℕ) : Decidable (SubtreeSupport T i k) :=
  inferInstanceAs (Decidable ((i, i + k) ∈ treeSpans T.val 0))

/-- For proper intervals (`2 ≤ k ≤ N - 1`), sub-tree support is membership in the
corresponding boundary-facet bracket of `PartialBracketing N`. -/
theorem subtreeSupport_iff_mem_partialBracketing {N i k : ℕ}
    (hk : 2 ≤ k) (hkN : k < N) (hi : i + k ≤ N) (T : FullBracketing N) :
    SubtreeSupport T i k ↔
      spanToBracket (i, i + k) ⟨⟨Nat.zero_le i, by omega, by omega⟩, by
        intro h; have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; omega⟩ ∈
          (treePartialBracketing T).val := by
  have hne : (i, i + k) ≠ (0, N) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    omega
  have hvalid : SpanValid 0 N (i, i + k) ∧ (i, i + k) ≠ (0, N) :=
    ⟨⟨Nat.zero_le i, by omega, by omega⟩, hne⟩
  constructor
  · intro hmem
    have hmem' : (i, i + k) ∈ treeProperSpans T := Finset.mem_erase.mpr ⟨hne, hmem⟩
    rw [← treePartialBracketing_spans T] at hmem'
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp hmem'
    have hsub : b = spanToBracket (i, i + k) hvalid := by
      apply bracketSpan_injective N
      exact hbeq
    rwa [← hsub]
  · intro hb
    have hmem : bracketSpan (spanToBracket (i, i + k) hvalid) ∈
        properBracketSpans (treePartialBracketing T).val := Finset.mem_image.mpr ⟨_, hb, rfl⟩
    rw [treePartialBracketing_spans T] at hmem
    exact (Finset.mem_erase.mp hmem).2

/-- **Theorem 2.1 (Operadic Factorization).**
Grafting at leaf `j = i` gives a constructive bijection between
`FullBracketing (N - k + 1) × FullBracketing k` and
`{ T : FullBracketing N // SubtreeSupport T i k }`. -/
def operadicFactorizationEquiv (N k i : ℕ) (hk : 2 ≤ k) (hi : i + k ≤ N) :
    FullBracketing (N - k + 1) × FullBracketing k ≃
      { T : FullBracketing N // SubtreeSupport T i k } where
  toFun p :=
    let t_out := p.1
    let t_in := p.2
    have hj : i < t_out.val.numLeaves := by rw [t_out.property]; omega
    have hleaves : (graftTree t_out.val i t_in.val).numLeaves = N := by
      rw [graftTree_numLeaves t_out.val t_in.val i hj, t_out.property, t_in.property]
      omega
    have hmem : SubtreeSupport ⟨graftTree t_out.val i t_in.val, hleaves⟩ i k := by
      have hm := graftTree_mem_treeSpans t_out.val t_in.val 0 i hj (by rw [t_in.property]; exact hk)
      dsimp [SubtreeSupport]
      simpa only [Nat.zero_add, t_in.property] using hm
    ⟨⟨graftTree t_out.val i t_in.val, hleaves⟩, hmem⟩
  invFun T :=
    have hmem : (i, i + k) ∈ treeSpans T.val.val 0 := T.property
    ⟨⟨contractAt T.val.val 0 i k, by
        rw [contractAt_numLeaves T.val.val 0 i k hk hmem, T.val.property]⟩,
     ⟨extractAt T.val.val 0 i k, extractAt_numLeaves T.val.val 0 i k hk hmem⟩⟩
  left_inv p := by
    ext1
    · apply Subtype.ext
      have hj : i < p.1.val.numLeaves := by rw [p.1.property]; omega
      have hkt : 2 ≤ p.2.val.numLeaves := by rw [p.2.property]; exact hk
      have h := contractAt_graftTree p.1.val p.2.val 0 i hj hkt
      simpa only [Nat.zero_add, p.2.property] using h
    · apply Subtype.ext
      have hj : i < p.1.val.numLeaves := by rw [p.1.property]; omega
      have hkt : 2 ≤ p.2.val.numLeaves := by rw [p.2.property]; exact hk
      have h := extractAt_graftTree p.1.val p.2.val 0 i hj hkt
      simpa only [Nat.zero_add, p.2.property] using h
  right_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    have h := graftTree_contractAt_extractAt T.val.val 0 i k hk T.property
    simpa only [Nat.sub_zero] using h

/-- **Theorem 2.1 (Fiber Cardinality).**
For any fixed contiguous interval `[i, i + k)` of length `k` (`2 ≤ k ≤ N`),
the number of trees in `FullBracketing N` supporting `[i, i + k)` is `C_{k-1} * C_{N-k}`. -/
theorem subtree_fiber_card (N k i : ℕ) (hk : 2 ≤ k) (hi : i + k ≤ N) :
    Fintype.card { T : FullBracketing N // SubtreeSupport T i k } =
      catalan (k - 1) * catalan (N - k) := by
  rw [Fintype.card_congr (operadicFactorizationEquiv N k i hk hi).symm, Fintype.card_prod]
  rw [fullBracketing_card_of_pos k (by omega), fullBracketing_card_of_pos (N - k + 1) (by omega)]
  rw [Nat.add_sub_cancel, mul_comm]

end SupportAndFactorization

section GlobalSumAndCorollary

attribute [local instance] instFintypeFullBracketingAll

/-- Total number of occurrences of complete `k`-leaf sub-tree components across all
trees in `FullBracketing N`, summed over all contiguous intervals `i : Fin (N - k + 1)`. -/
def globalSubtreeMultiplicity (N k : ℕ) : ℕ :=
  ∑ i : Fin (N - k + 1), Fintype.card { T : FullBracketing N // SubtreeSupport T i.val k }

/-- **Double Counting:** Summing fiber cardinalities over intervals equals summing the
number of length-`k` internal spans over all trees `T ∈ FullBracketing N`. -/
theorem globalSubtreeMultiplicity_eq_tree_sum (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) :
    globalSubtreeMultiplicity N k =
      ∑ T : FullBracketing N, ((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card := by
  dsimp [globalSubtreeMultiplicity]
  have hcard : ∀ i : Fin (N - k + 1),
      Fintype.card { T : FullBracketing N // SubtreeSupport T i.val k } =
        ∑ T : FullBracketing N, if SubtreeSupport T i.val k then 1 else 0 := by
    intro i
    rw [Fintype.card_subtype, Finset.card_filter]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_boole, Nat.cast_id]
  refine Finset.card_nbij (fun i => (i.val, i.val + k)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi, by omega⟩
  · intro a _ b _ hab
    ext
    exact congrArg Prod.fst hab
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    have hv := treeSpans_valid T.val 0 p hp.1
    rw [T.property] at hv
    dsimp [SpanValid] at hv
    refine ⟨⟨p.1, by omega⟩, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change (p.1, p.1 + k) ∈ treeSpans T.val 0
      have hp2 : p.1 + k = p.2 := by omega
      have hpair : (p.1, p.1 + k) = p := Prod.ext rfl hp2
      rw [hpair]
      exact hp.1
    · change (p.1, p.1 + k) = p
      exact Prod.ext rfl (by omega)

/-- **Theorem 3.1 (Global Sub-Associahedron Multiplicity).**
For `2 ≤ k ≤ N`, `Φ(N, k) = C_{k-1} * choose (2 * (N - k)) (N - k)`. -/
theorem globalSubtreeMultiplicity_eq (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) :
    globalSubtreeMultiplicity N k = catalan (k - 1) * Nat.choose (2 * (N - k)) (N - k) := by
  dsimp [globalSubtreeMultiplicity]
  have hterm : ∀ i : Fin (N - k + 1),
      Fintype.card { T : FullBracketing N // SubtreeSupport T i.val k } =
        catalan (k - 1) * catalan (N - k) := fun i =>
    subtree_fiber_card N k i.val hk (by omega)
  simp_rw [hterm, Finset.sum_const, Finset.card_fin, smul_eq_mul]
  calc
    (N - k + 1) * (catalan (k - 1) * catalan (N - k))
      = catalan (k - 1) * ((N - k + 1) * catalan (N - k)) := by ring
    _ = catalan (k - 1) * (N - k).centralBinom := by
        rw [succ_mul_catalan_eq_centralBinom]
    _ = catalan (k - 1) * Nat.choose (2 * (N - k)) (N - k) := by
        rw [Nat.centralBinom_eq_two_mul_choose]

/-- **Corollary 4.1 (Central Binomial Multiplicity for `k = 2`).**
For elementary binary composition nodes (`k = 2`), `Φ(N, 2) = choose (2 * N - 4) (N - 2)`. -/
theorem globalSubtreeMultiplicity_k2 (N : ℕ) (hN : 2 ≤ N) :
    globalSubtreeMultiplicity N 2 = Nat.choose (2 * N - 4) (N - 2) := by
  rw [globalSubtreeMultiplicity_eq N 2 (le_refl 2) hN]
  simp only [Nat.reduceSub, catalan_one, one_mul]
  congr 1
  omega

end GlobalSumAndCorollary

section GeometricFacetBridge

attribute [local instance] instFintypeFullBracketingAll
attribute [local instance] Classical.propDecidable

/-- The polygon diagonal of an `(n + 3)`-gon corresponding to a proper interval `[i, i + k)`
(`2 ≤ k < n + 2`, `i + k ≤ n + 2`). -/
def subtreeFacetDiagonal (n i k : ℕ) (hk : 2 ≤ k) (hkN : k < n + 2) (hi : i + k ≤ n + 2) :
    PolygonDiagonal (n + 2) where
  a := ⟨i, by omega⟩
  b := ⟨i + k, by omega⟩
  gap := by dsimp; omega
  not_boundary := by
    intro h
    have h1 : i = 0 := h.1
    have h2 : i + k = n + 2 := h.2
    omega

theorem subtreeFacet_leftArity (n i k : ℕ) (hk : 2 ≤ k) (hkN : k < n + 2) (hi : i + k ≤ n + 2) :
    facetLeftArity (subtreeFacetDiagonal n i k hk hkN hi) = k := by
  dsimp [facetLeftArity, subtreeFacetDiagonal]
  omega

theorem subtreeFacet_rightArity (n i k : ℕ) (hk : 2 ≤ k) (hkN : k < n + 2) (hi : i + k ≤ n + 2) :
    facetRightArity (subtreeFacetDiagonal n i k hk hkN hi) = n + 2 - k + 1 := by
  dsimp [facetRightArity, facetLeftArity, subtreeFacetDiagonal]
  omega

/-- **Geometric Facet Type (`K_k × K_{N-k+1}`):** For `N = n + 2` and a proper interval
`[i, i + k)` (`2 ≤ k ≤ N - 1`), the supporting facet `F_I` of `LodayPolytope n` has the
product face order `K_k × K_{N - k + 1}`. -/
theorem subtreeFacet_product_orderIso (n i k : ℕ)
    (hk : 2 ≤ k) (hkN : k < n + 2) (hi : i + k ≤ n + 2) :
    Nonempty (LodayFacetFaces n (subtreeFacetDiagonal n i k hk hkN hi) ≃o
      LodayExposedFace (k - 2) × LodayExposedFace (n + 2 - k - 1)) := by
  have iso := Loday_facet_geometric_product_orderIso n (subtreeFacetDiagonal n i k hk hkN hi)
  rw [subtreeFacet_leftArity, subtreeFacet_rightArity] at iso
  have hr : n + 2 - k + 1 - 2 = n + 2 - k - 1 := by omega
  rw [hr] at iso
  exact ⟨iso⟩

/-- **Geometric Vertex–Facet Incidence:** For `N = n + 2` and a proper interval `[i, i + k)`
(`2 ≤ k ≤ N - 1`), `SubtreeSupport T i k` holds if and only if the Loday vertex `lodayPoint n T`
lies on the supporting boundary facet `F_I` of `LodayPolytope n`. -/
theorem subtreeSupport_iff_loday_vertex_on_facet (n i k : ℕ)
    (hk : 2 ≤ k) (hkN : k < n + 2) (hi : i + k ≤ n + 2) (T : FullBracketing (n + 2)) :
    SubtreeSupport T i k ↔
      lodayPoint n T ∈
        (polygon_loday_face_orderIso n
          (singletonPolygonFace (subtreeFacetDiagonal n i k hk hkN hi))).val := by
  let d := subtreeFacetDiagonal n i k hk hkN hi
  let b : ProperBracket (n + 2) := (bracketDiagonalEquiv (n + 2)).symm d
  have hb_span : bracketSpan b = (i, i + k) := rfl
  have hsingle : (partialBracketing_face_orderIso (n + 2)).symm (singletonPolygonFace d) =
      ⟨{b}, by
        intro p hp q hq
        rw [Finset.mem_singleton.mp hp, Finset.mem_singleton.mp hq]
        dsimp [BracketCompatible]; omega⟩ := by
    apply (partialBracketing_face_orderIso (n + 2)).injective
    rw [(partialBracketing_face_orderIso (n + 2)).apply_symm_apply]
    apply Subtype.ext
    change ({b} : Finset (ProperBracket (n + 2))).map (bracketDiagonalEquiv (n + 2)).toEmbedding =
      {d}
    rw [Finset.map_singleton]
    rfl
  change SubtreeSupport T i k ↔
    lodayPoint n T ∈
      (bracketExposedFace n ((partialBracketing_face_orderIso (n + 2)).symm
        (singletonPolygonFace d))).val
  rw [hsingle]
  change SubtreeSupport T i k ↔
    lodayPoint n T ∈ LodayPolytope n ∧
      ∀ c ∈ ({b} : Finset (ProperBracket (n + 2))),
        intervalLinear n c.left.val c.right.val (lodayPoint n T) =
          Nat.choose (c.right.val - c.left.val) 2
  simp only [Finset.mem_singleton, forall_eq]
  have hpoly : lodayPoint n T ∈ LodayPolytope n :=
    subset_convexHull ℝ _ (Set.mem_range_self T)
  have htight := lodayPoint_tight_iff n T b
  rw [hb_span] at htight
  rw [htight]
  exact ⟨fun h => ⟨hpoly, h⟩, fun h => h.2⟩

/-- **Theorem 3.1 (Geometric Incidence Form):** For `N = n + 2` and proper arity
`2 ≤ k ≤ N - 1`, `Φ(N, k)` counts the total vertex–facet incidences
`(T, F_I)` across `LodayPolytope n` with `F_I ≅ K_k × K_{N - k + 1}`. -/
theorem globalSubtreeMultiplicity_eq_loday_incidence (n k : ℕ)
    (hk : 2 ≤ k) (hkN : k < n + 2) :
    globalSubtreeMultiplicity (n + 2) k =
      ∑ i : Fin (n + 2 - k + 1),
        let hi : i.val + k ≤ n + 2 := by omega
        Fintype.card { T : FullBracketing (n + 2) //
          lodayPoint n T ∈
            (polygon_loday_face_orderIso n
              (singletonPolygonFace (subtreeFacetDiagonal n i.val k hk hkN hi))).val } := by
  dsimp [globalSubtreeMultiplicity]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : i.val + k ≤ n + 2 := by omega
  exact Fintype.card_congr
    (Equiv.subtypeEquivRight
      (fun T => subtreeSupport_iff_loday_vertex_on_facet n i.val k hk hkN hi T))

end GeometricFacetBridge

section DensityAndAsymptotics

attribute [local instance] instFintypeFullBracketingAll

/-- Expected number of complete sub-trees of arity `k` in a uniform random tree
`T ∈ FullBracketing N`. -/
noncomputable def expectedSubtreeDensity (N k : ℕ) : ℝ :=
  (globalSubtreeMultiplicity N k : ℝ) / (Fintype.card (FullBracketing N) : ℝ)

/-- **Theorem 5.1 (Expected Density as Average over Trees).** -/
theorem expectedSubtreeDensity_eq_tree_avg (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) :
    expectedSubtreeDensity N k =
      (∑ T : FullBracketing N,
        (((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card : ℝ)) /
        (Fintype.card (FullBracketing N) : ℝ) := by
  dsimp [expectedSubtreeDensity]
  rw [globalSubtreeMultiplicity_eq_tree_sum N k hk hkN]
  push_cast
  rfl

private theorem fullBracketing_nonempty_of_pos (N : ℕ) (hN : 1 ≤ N) :
    Nonempty (FullBracketing N) := by
  have hcb : 0 < Nat.centralBinom (N - 1) := Nat.centralBinom_pos (N - 1)
  have hcat : 0 < catalan (N - 1) := by
    by_contra h0
    have h0' : catalan (N - 1) = 0 := by omega
    have hmul := succ_mul_catalan_eq_centralBinom (N - 1)
    rw [h0', mul_zero] at hmul
    omega
  have hpos : 0 < Fintype.card (FullBracketing N) := by
    rw [fullBracketing_card_of_pos N hN]
    exact hcat
  exact Fintype.card_pos_iff.mp hpos

/-- **Theorem 5.1 (Uniform Probability Expectation Form).**
Under the uniform distribution `PMF.uniformOfFintype (FullBracketing N)`,
`expectedSubtreeDensity N k` equals the expectation of the `k`-leaf subtree count. -/
theorem expectedSubtreeDensity_eq_uniform_expectation (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N)
    [Nonempty (FullBracketing N)] :
    expectedSubtreeDensity N k =
      ∑ T : FullBracketing N,
        (PMF.uniformOfFintype (FullBracketing N) T).toReal *
          (((treeSpans T.val 0).filter (fun p => p.2 - p.1 = k)).card : ℝ) := by
  rw [expectedSubtreeDensity_eq_tree_avg N k hk hkN]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← Finset.mul_sum, div_eq_inv_mul]

/-- **Theorem 5.2 (Expected Density per Vertex).** -/
theorem expectedSubtreeDensity_eq (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) :
    expectedSubtreeDensity N k =
      (catalan (k - 1) : ℝ) * (Nat.choose (2 * (N - k)) (N - k) : ℝ) /
        ((Nat.choose (2 * (N - 1)) (N - 1) : ℝ) / (N : ℝ)) := by
  have hN : 1 ≤ N := by omega
  dsimp [expectedSubtreeDensity]
  rw [globalSubtreeMultiplicity_eq N k hk hkN, fullBracketing_card_of_pos N hN]
  have hcat : (catalan (N - 1) : ℝ) = (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) / (N : ℝ) := by
    have hmul : N * catalan (N - 1) = Nat.choose (2 * (N - 1)) (N - 1) := by
      have h := succ_mul_catalan_eq_centralBinom (N - 1)
      rw [Nat.sub_add_cancel hN, Nat.centralBinom_eq_two_mul_choose] at h
      exact h
    have hNpos : (N : ℝ) ≠ 0 := by positivity
    have hmulR : (N : ℝ) * (catalan (N - 1) : ℝ) = (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) := by
      exact_mod_cast hmul
    field_simp [hNpos]
    linarith
  rw [hcat]
  push_cast
  rfl

/-- Ratio of central binomial coefficients expressed as a finite telescoping product. -/
private noncomputable def centralBinomRatio (m N : ℕ) : ℝ :=
  (Nat.choose (2 * (N - (m + 1))) (N - (m + 1)) : ℝ) /
    (Nat.choose (2 * (N - 1)) (N - 1) : ℝ)

private theorem centralBinomRatio_zero (N : ℕ) (_hN : 1 ≤ N) :
    centralBinomRatio 0 N = 1 := by
  dsimp [centralBinomRatio]
  have hpos : (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) ≠ 0 := by
    rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero (N - 1))
  exact div_self hpos

private theorem centralBinomRatio_succ (m N : ℕ) (hm : m + 2 ≤ N) :
    centralBinomRatio (m + 1) N =
      centralBinomRatio m N *
        (((N : ℝ) - ((m : ℝ) + 1)) / (2 * (2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1))) := by
  dsimp [centralBinomRatio]
  set r := N - (m + 2)
  have hr : N - (m + 1) = r + 1 := by omega
  have hrR : (N : ℝ) - ((m : ℝ) + 1) = (r : ℝ) + 1 := by
    have hnat : N = r + (m + 1) + 1 := by omega
    have hcast : (N : ℝ) = (r : ℝ) + ((m : ℝ) + 1) + 1 := by exact_mod_cast hnat
    linarith
  have hstep : ((r + 1 : ℕ) : ℝ) * (Nat.choose (2 * (r + 1)) (r + 1) : ℝ) =
      2 * (2 * (r : ℝ) + 1) * (Nat.choose (2 * r) r : ℝ) := by
    have hnat := Nat.succ_mul_centralBinom_succ r
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hnat
    exact_mod_cast hnat
  have hden0 : (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) ≠ 0 := by
    rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero (N - 1))
  have hcr1 : (Nat.choose (2 * (r + 1)) (r + 1) : ℝ) ≠ 0 := by
    rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero (r + 1))
  have h2r1 : (2 * (r : ℝ) + 1) ≠ 0 := by positivity
  rw [hr, hrR]
  have hden2 : 2 * (2 * ((r : ℝ) + 1) - 1) = 2 * (2 * (r : ℝ) + 1) := by ring
  rw [hden2]
  have hcb : (Nat.choose (2 * r) r : ℝ) =
      (Nat.choose (2 * (r + 1)) (r + 1) : ℝ) * (((r : ℝ) + 1) / (2 * (2 * (r : ℝ) + 1))) := by
    field_simp [h2r1]
    have hstep' : ((r : ℝ) + 1) * (Nat.choose (2 * (r + 1)) (r + 1) : ℝ) =
        2 * (2 * (r : ℝ) + 1) * (Nat.choose (2 * r) r : ℝ) := by
      push_cast at hstep ⊢; linarith
    linarith
  rw [hcb]
  ring

private theorem tendsto_const_div_nat (c : ℝ) :
    Tendsto (fun N : ℕ => c / (N : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

private theorem tendsto_centralBinomRatio (m : ℕ) :
    Tendsto (fun N : ℕ => centralBinomRatio m N) atTop (𝓝 ((1 / 4 : ℝ) ^ m)) := by
  induction m with
  | zero =>
    simp only [pow_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (centralBinomRatio_zero N hN).symm
  | succ m ih =>
    have hfactor : Tendsto
        (fun N : ℕ =>
          ((N : ℝ) - ((m : ℝ) + 1)) / (2 * (2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1)))
        atTop (𝓝 (1 / 4 : ℝ)) := by
      have hm := tendsto_const_div_nat ((m : ℝ) + 1)
      have h1 := tendsto_const_div_nat (1 : ℝ)
      have hdiv : Tendsto (fun N : ℕ =>
          (1 - ((m : ℝ) + 1) / (N : ℝ)) /
            (2 * (2 * (1 - ((m : ℝ) + 1) / (N : ℝ)) - 1 / (N : ℝ))))
          atTop (𝓝 ((1 - 0) / (2 * (2 * (1 - 0) - 0)))) :=
        Tendsto.div (tendsto_const_nhds.sub hm)
          (tendsto_const_nhds.mul ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hm)).sub h1))
          (by norm_num)
      have hlim : (1 - (0 : ℝ)) / (2 * (2 * (1 - 0) - 0)) = 1 / 4 := by norm_num
      rw [hlim] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [eventually_ge_atTop (m + 2)] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by
        have : 1 ≤ N := by omega
        positivity
      have hden : 2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1 ≠ 0 := by
        have : (m : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hnum : 1 - ((m : ℝ) + 1) / (N : ℝ) = ((N : ℝ) - ((m : ℝ) + 1)) / (N : ℝ) := by
        field_simp [hN0]
      have hden_eq : 2 * (2 * (1 - ((m : ℝ) + 1) / (N : ℝ)) - 1 / (N : ℝ)) =
          2 * (2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1) / (N : ℝ) := by
        field_simp [hN0]
      rw [hden_eq, hnum]
      field_simp [hN0, hden]
    have hprod := ih.mul hfactor
    rw [← pow_succ] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop (m + 2)] with N hN
    exact (centralBinomRatio_succ m N hN).symm

private theorem tendsto_scaled_centralBinomRatio_sub (m : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) * (centralBinomRatio m N - (1 / 4 : ℝ) ^ m))
      atTop (𝓝 ((m : ℝ) / (2 * 4 ^ m))) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, pow_zero, zero_div]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [centralBinomRatio_zero N hN]
    ring
  | succ m ih =>
    have htail : Tendsto (fun N : ℕ =>
        (N : ℝ) / (4 * (2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1)))
        atTop (𝓝 (1 / 8 : ℝ)) := by
      have hm := tendsto_const_div_nat (2 * (m : ℝ) + 3)
      have hdiv : Tendsto (fun N : ℕ => (1 : ℝ) / (4 * (2 - (2 * (m : ℝ) + 3) / (N : ℝ))))
          atTop (𝓝 (1 / (4 * (2 - 0)))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.mul (tendsto_const_nhds.sub hm)) (by norm_num)
      have hlim : (1 : ℝ) / (4 * (2 - 0)) = 1 / 8 := by norm_num
      rw [hlim] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [eventually_ge_atTop (m + 2)] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by
        have : 1 ≤ N := by omega
        positivity
      have hden : 2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1 ≠ 0 := by
        have : (m : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hden_eq : 2 - (2 * (m : ℝ) + 3) / (N : ℝ) =
          (2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1) / (N : ℝ) := by
        field_simp [hN0]
        ring
      rw [hden_eq]
      field_simp [hN0, hden]
    have hcomb := (tendsto_const_nhds (x := (1 / 4 : ℝ)).mul ih).add
      ((tendsto_centralBinomRatio m).mul htail)
    have hlim : (1 / 4 : ℝ) * ((m : ℝ) / (2 * 4 ^ m)) + (1 / 4 : ℝ) ^ m * (1 / 8 : ℝ) =
        (((m + 1 : ℕ) : ℝ) / (2 * 4 ^ (m + 1))) := by
      push_cast
      rw [one_div_pow, pow_succ]
      ring
    rw [hlim] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [eventually_ge_atTop (m + 2)] with N hN
    rw [centralBinomRatio_succ m N hN]
    set d := 2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1
    have hd : d ≠ 0 := by
      have : (m : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hN
      dsimp [d]
      linarith
    have hsplit : ((N : ℝ) - ((m : ℝ) + 1)) / (2 * d) = 1 / 4 + 1 / (4 * d) := by
      field_simp [hd]
      dsimp [d]
      ring
    rw [hsplit]
    ring

/-- **Theorem 5.2 (Asymptotic Constant Limit).**
For fixed `k ≥ 2`, `E[n_k](N) - (C_{k-1} / 4^(k-1)) * N` converges to
`C_{k-1} * (k - 1) / (2 * 4^(k-1))` as `N → ∞`. -/
theorem expectedSubtreeDensity_sub_linear_tendsto (k : ℕ) (hk : 2 ≤ k) :
    Tendsto
      (fun N : ℕ => expectedSubtreeDensity N k - ((catalan (k - 1) : ℝ) / 4 ^ (k - 1)) * (N : ℝ))
      atTop (𝓝 ((catalan (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1)))) := by
  have hscaled := tendsto_const_nhds (x := (catalan (k - 1) : ℝ)).mul
    (tendsto_scaled_centralBinomRatio_sub (k - 1))
  have hlim : (catalan (k - 1) : ℝ) * (((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1))) =
      (catalan (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1)) := by ring
  rw [hlim] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  rw [expectedSubtreeDensity_eq N k hk hN]
  have hN0 : (N : ℝ) ≠ 0 := by
    have : 1 ≤ N := by omega
    positivity
  have hden : (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) ≠ 0 := by
    rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero (N - 1))
  have hk1 : (k - 1) + 1 = k := by omega
  have hcr : centralBinomRatio (k - 1) N =
      (Nat.choose (2 * (N - k)) (N - k) : ℝ) / (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) := by
    dsimp [centralBinomRatio]
    rw [hk1]
  rw [hcr, one_div_pow]
  field_simp [hN0, hden]

/-- **Theorem 5.2 (Asymptotic Scaling Law, `O(1)` Remainder).**
For fixed `k ≥ 2`, `E[n_k](N) - (C_{k-1} / 4^(k-1)) * N = O(1)` as `N → ∞`. -/
theorem expectedSubtreeDensity_asymptotic (k : ℕ) (hk : 2 ≤ k) :
    (fun N : ℕ => expectedSubtreeDensity N k - ((catalan (k - 1) : ℝ) / 4 ^ (k - 1)) * (N : ℝ))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
  (expectedSubtreeDensity_sub_linear_tendsto k hk).isBigO_one ℝ

private theorem tendsto_second_centralBinomRatio (m : ℕ) :
    ∃ L : ℝ, Tendsto
      (fun N : ℕ =>
        (N : ℝ) * ((N : ℝ) * (centralBinomRatio m N - (1 / 4 : ℝ) ^ m) - (m : ℝ) / (2 * 4 ^ m)))
      atTop (𝓝 L) := by
  induction m with
  | zero =>
    refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Nat.cast_zero, pow_zero, zero_div, centralBinomRatio_zero N hN, sub_self, mul_zero]
  | succ m ih =>
    obtain ⟨L, hL⟩ := ih
    have htail : Tendsto (fun N : ℕ =>
        (N : ℝ) / (4 * (2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1)))
        atTop (𝓝 (1 / 8 : ℝ)) := by
      have hm := tendsto_const_div_nat (2 * (m : ℝ) + 3)
      have hdiv : Tendsto (fun N : ℕ => (1 : ℝ) / (4 * (2 - (2 * (m : ℝ) + 3) / (N : ℝ))))
          atTop (𝓝 (1 / (4 * (2 - 0)))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.mul (tendsto_const_nhds.sub hm)) (by norm_num)
      have hlim : (1 : ℝ) / (4 * (2 - 0)) = 1 / 8 := by norm_num
      rw [hlim] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [eventually_ge_atTop (m + 2)] with N hN
      have hN1 : 1 ≤ N := by omega
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      have hden : 2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1 ≠ 0 := by
        have : (m : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hden_eq : 2 - (2 * (m : ℝ) + 3) / (N : ℝ) =
          (2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1) / (N : ℝ) := by
        field_simp [hN0]; ring
      rw [hden_eq]
      field_simp [hN0, hden]
    have hrem : Tendsto (fun N : ℕ =>
        (N : ℝ) * ((N : ℝ) / (4 * (2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1)) - 1 / 8))
        atTop (𝓝 ((2 * (m : ℝ) + 3) / 16)) := by
      have hm := tendsto_const_div_nat (2 * (m : ℝ) + 3)
      have hdiv : Tendsto (fun N : ℕ =>
          (2 * (m : ℝ) + 3) / (8 * (2 - (2 * (m : ℝ) + 3) / (N : ℝ))))
          atTop (𝓝 ((2 * (m : ℝ) + 3) / (8 * (2 - 0)))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.mul (tendsto_const_nhds.sub hm)) (by norm_num)
      have hlim : (2 * (m : ℝ) + 3) / (8 * (2 - 0)) = (2 * (m : ℝ) + 3) / 16 := by norm_num
      rw [hlim] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [eventually_ge_atTop (m + 2)] with N hN
      have hN1 : 1 ≤ N := by omega
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      have hden : 2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1 ≠ 0 := by
        have : (m : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hden_eq : 2 - (2 * (m : ℝ) + 3) / (N : ℝ) =
          (2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1) / (N : ℝ) := by
        field_simp [hN0]; ring
      rw [hden_eq]
      set d := 2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1
      have hd : d ≠ 0 := hden
      field_simp [hN0, hd]
      dsimp [d]
      ring
    have hcomb :=
      ((tendsto_const_nhds (x := (1 / 4 : ℝ)).mul hL).add
        ((tendsto_scaled_centralBinomRatio_sub m).mul htail)).add
        (tendsto_const_nhds (x := (1 / 4 : ℝ) ^ m).mul hrem)
    refine ⟨_, hcomb.congr' ?_⟩
    filter_upwards [eventually_ge_atTop (m + 2)] with N hN
    rw [centralBinomRatio_succ m N hN]
    set d := 2 * ((N : ℝ) - ((m : ℝ) + 1)) - 1
    have hd : d ≠ 0 := by
      have : (m : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hN
      dsimp [d]; linarith
    have hsplit : ((N : ℝ) - ((m : ℝ) + 1)) / (2 * d) = 1 / 4 + 1 / (4 * d) := by
      field_simp [hd]; dsimp [d]; ring
    rw [hsplit]
    push_cast
    simp only [one_div_pow, pow_succ]
    field_simp [hd]
    ring

/-- **Theorem 5.2 (Exact `O(1 / N)` Remainder Bound).**
For fixed `k ≥ 2`,
`E[n_k](N) - (C_{k-1} / 4^(k-1)) * N - C_{k-1} * (k - 1) / (2 * 4^(k-1)) = O(1 / N)`. -/
theorem expectedSubtreeDensity_asymptotic_inv (k : ℕ) (hk : 2 ≤ k) :
    (fun N : ℕ =>
      expectedSubtreeDensity N k -
        ((catalan (k - 1) : ℝ) / 4 ^ (k - 1)) * (N : ℝ) -
        (catalan (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1)))
      =O[atTop] (fun N : ℕ => (1 : ℝ) / (N : ℝ)) := by
  obtain ⟨L, hL⟩ := tendsto_second_centralBinomRatio (k - 1)
  have hscaled := (tendsto_const_nhds (x := (catalan (k - 1) : ℝ)).mul hL).isBigO_one ℝ
  have hmul :
      (fun N : ℕ => (N : ℝ) *
        (expectedSubtreeDensity N k -
          ((catalan (k - 1) : ℝ) / 4 ^ (k - 1)) * (N : ℝ) -
          (catalan (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1))))
        =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    refine hscaled.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_ge_atTop k] with N hN
    rw [expectedSubtreeDensity_eq N k hk hN]
    have hN1 : 1 ≤ N := by omega
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hden : (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) ≠ 0 := by
      rw [← Nat.centralBinom_eq_two_mul_choose]
      exact Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero (N - 1))
    have hk1 : (k - 1) + 1 = k := by omega
    have hcr : centralBinomRatio (k - 1) N =
        (Nat.choose (2 * (N - k)) (N - k) : ℝ) / (Nat.choose (2 * (N - 1)) (N - 1) : ℝ) := by
      dsimp [centralBinomRatio]; rw [hk1]
    rw [hcr, one_div_pow]
    field_simp [hN0, hden]
  rw [Asymptotics.isBigO_iff] at hmul ⊢
  obtain ⟨c, hc⟩ := hmul
  refine ⟨c, ?_⟩
  filter_upwards [hc, eventually_ge_atTop 1] with N hNc hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hle : ‖(N : ℝ)‖ *
      ‖expectedSubtreeDensity N k -
        ((catalan (k - 1) : ℝ) / 4 ^ (k - 1)) * (N : ℝ) -
        (catalan (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1))‖ ≤ c * 1 := by
    simpa [norm_mul] using hNc
  calc
    ‖expectedSubtreeDensity N k -
        ((catalan (k - 1) : ℝ) / 4 ^ (k - 1)) * (N : ℝ) -
        (catalan (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1))‖
      = (‖(N : ℝ)‖)⁻¹ * (‖(N : ℝ)‖ *
          ‖expectedSubtreeDensity N k -
            ((catalan (k - 1) : ℝ) / 4 ^ (k - 1)) * (N : ℝ) -
            (catalan (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) / (2 * 4 ^ (k - 1))‖) := by
          field_simp [ne_of_gt hNpos]
    _ ≤ (‖(N : ℝ)‖)⁻¹ * (c * 1) := by gcongr
    _ = c * ‖(1 : ℝ) / (N : ℝ)‖ := by
          rw [norm_div, norm_one, Real.norm_of_nonneg hNpos.le]
          ring

end DensityAndAsymptotics

end FunctorialGeometry
