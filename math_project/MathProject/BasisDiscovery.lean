/-
Copyright (c) 2026 Shivansh Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shivansh Singh
-/

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Data.Set.Basic

/-!
# Basis Discovery Algorithm
This file contains the core definitions for the basis discovery algorithm.
-/

namespace BasisDiscovery

variable {L : Type} [CompleteLattice L]
/- 
This typeclass acts as a firewall against circular logic. 
By requiring a Well-Founded order, it mathematically guarantees there are no 
infinite descending chains or circular priority loops (e.g., A < B < C < A), 
ensuring a fundamental "bottom" always exists.
-/
variable {J : Type} [LinearOrder J] [WellFoundedLT J]
variable (embed : J → L)

/--
This axiom mathematically guarantees that the universe is built out of discrete, 
fundamental building blocks (atoms/join-irreducibles). 
It acts as a firewall to prevent the algorithm from running on continuous spaces 
or fractals, which are infinitely divisible and possess no fundamental generators.
-/
class IsGenerated {L J : Type} [CompleteLattice L] (embed : J → L) : Prop where
  eq_iSup : ∀ x : L, x = ⨆ (j : J) (_ : embed j ≤ x), embed j

variable [IsGenerated embed]

omit [LinearOrder J] [WellFoundedLT J] in
lemma candidates_nonempty (x : L) (h : x < ⊤) : { j : J | ¬ (embed j ≤ x) }.Nonempty := by
  by_contra h_contra
  rw [Set.not_nonempty_iff_eq_empty] at h_contra
  have h_all : ∀ j, embed j ≤ x := by
    intro j
    by_contra h_not_le
    have h_in : j ∈ { j : J | ¬ (embed j ≤ x) } := h_not_le
    rw [h_contra] at h_in
    exact h_in
  have h_top_le_x : (⊤ : L) ≤ x := by
    have h_top := IsGenerated.eq_iSup (embed := embed) ⊤
    rw [h_top]
    apply iSup_le
    intro j
    apply iSup_le
    intro _
    exact h_all j
  have h_eq : x = ⊤ := top_le_iff.mp h_top_le_x
  exact h.ne h_eq

open Classical in
/--
The `open Classical` statement invokes the Axiom of Choice.
It acts as a firewall against strictly Constructive mathematics, allowing the 
algorithm to mathematically "choose" a minimum generator out of uncountably 
infinite sets where computing one is physically impossible.
-/
noncomputable def fixedPriorityPhi (x : L) (h : x < ⊤) : J :=
  let candidates := { j : J | ¬ (embed j ≤ x) }
  have h_nonempty : candidates.Nonempty := candidates_nonempty embed x h
  WellFounded.min wellFounded_lt candidates h_nonempty

theorem novelty_of_fixedPriorityPhi (x : L) (h : x < ⊤) :
    ¬ (embed (fixedPriorityPhi embed x h) ≤ x) :=
  WellFounded.min_mem wellFounded_lt { j : J | ¬ (embed j ≤ x) } (candidates_nonempty embed x h)

open Classical in
/--
The transfinite sequence of extracted generators across ordinals.
-/
noncomputable def xSeq (o : Ordinal) : L :=
  Ordinal.limitRecOn o
    (⊥ : L)
    (fun _ x => if h : x < ⊤ then x ⊔ embed (fixedPriorityPhi embed x h) else x)
    (fun a _ f => ⨆ (b : Ordinal) (hb : b < a), f b hb)

/--
The final supremum of all generators extracted across the transfinite sequence.
-/
noncomputable def sieveOutput : L :=
  ⨆ (o : Ordinal.{0}), xSeq embed o

end BasisDiscovery
