import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.EventuallyConst

open CategoryTheory
open CategoryTheory.Limits
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u
variable {A : Type u} [Category.{u} A] [Abelian A] [WellPowered.{u} A] [HasColimits A]
variable (U₀ : A)

-- 1. Prerequisites 
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
  intro hz
  exact h (eq_top_of_isZero_residual U₀ C hz)

lemma lt_cellular (C : Subobject U₀) (a : A) (i : a ⟶ cokernel C.arrow) (hi : Mono i)
    (ha : IsSimple a) :
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
    calc
      pullback.fst i (cokernel.π C.arrow) ≫ i = pullback.snd i (cokernel.π C.arrow) ≫ cokernel.π C.arrow := pullback.condition
      _ = (k ≫ C.arrow) ≫ cokernel.π C.arrow := by rw [← hk]
      _ = k ≫ (C.arrow ≫ cokernel.π C.arrow) := by rw [Category.assoc]
      _ = k ≫ 0 := by rw [cokernel.condition]
      _ = 0 := Limits.comp_zero
  have h_fst_zero : pullback.fst i (cokernel.π C.arrow) = 0 := by
    rw [← cancel_mono i]
    exact h_comp.trans (Limits.zero_comp).symm
  have h_epi : Epi (pullback.fst i (cokernel.π C.arrow)) := inferInstance
  rw [h_fst_zero] at h_epi
  have : Epi (0 : pullback i (cokernel.π C.arrow) ⟶ a) := h_epi
  have h_zero : IsZero a := IsZero.of_epi_zero (pullback i (cokernel.π C.arrow)) a
  exact ha.1 h_zero

-- 2. Successor Constructor
/-- Extracts a simple subobject from the residual and pulls it back. 
    If the residual is zero (exhausted), it returns C. -/
noncomputable def nextLoewy (C : Subobject U₀) (h_semi : IsSemiArtinian U₀) : Subobject U₀ :=
  if h : IsZero (residual U₀ C) then 
    C 
  else 
    let a := (h_semi C h).choose
    let i := (h_semi C h).choose_spec.choose
    haveI : Mono i := (h_semi C h).choose_spec.choose_spec.2
    haveI : Mono (pullback.snd i (cokernel.π C.arrow)) := pullback.snd_of_mono
    Subobject.mk (pullback.snd i (cokernel.π C.arrow))

lemma le_nextLoewy (C : Subobject U₀) (h_semi : IsSemiArtinian U₀) :
    C ≤ nextLoewy U₀ C h_semi := by
  dsimp [nextLoewy]
  split_ifs with h
  · exact le_rfl
  · let a := (h_semi C h).choose
    let i := (h_semi C h).choose_spec.choose
    have ha_simple := (h_semi C h).choose_spec.choose_spec.1
    have hi : Mono i := (h_semi C h).choose_spec.choose_spec.2
    have := lt_cellular U₀ C a i hi ha_simple
    exact this.le

-- 3. Transfinite Sequence
/-- Constructs the sequence natively inside the Subobject lattice. -/
noncomputable def loewySequence (h_semi : IsSemiArtinian U₀) (o : Ordinal.{u}) : Subobject U₀ :=
  Ordinal.limitRecOn o
    (⊥ : Subobject U₀)
    (fun _ C => nextLoewy U₀ C h_semi)
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

lemma loewySequence_limit (h_semi : IsSemiArtinian U₀) (o : Ordinal.{u}) (ho : Order.IsSuccLimit o) :
    loewySequence U₀ h_semi o = ⨆ (b : Ordinal.{u}) (_hb : b < o), loewySequence U₀ h_semi b := by
  dsimp [loewySequence]
  exact Ordinal.limitRecOn_limit o _ _ _ ho

lemma loewySequence_le (h_semi : IsSemiArtinian U₀) (o₁ o₂ : Ordinal.{u}) (h_le : o₁ ≤ o₂) :
    loewySequence U₀ h_semi o₁ ≤ loewySequence U₀ h_semi o₂ := by
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
      have step_le : loewySequence U₀ h_semi o₂ ≤ loewySequence U₀ h_semi (o₂ + 1) := by
        dsimp [loewySequence]
        rw [Ordinal.limitRecOn_add_one]
        exact le_nextLoewy U₀ (loewySequence U₀ h_semi o₂) h_semi
      exact ih_le.trans step_le
  | limit o₂ ho ih =>
    intro o₁ h₁
    rcases eq_or_lt_of_le h₁ with rfl | hlt
    · exact le_rfl
    · rw [loewySequence_limit U₀ h_semi o₂ ho]
      exact le_biSup_subobject U₀ o₂ o₁ hlt (fun b _ => loewySequence U₀ h_semi b)

lemma loewySequence_mono (h_semi : IsSemiArtinian U₀) :
    Monotone (loewySequence U₀ h_semi) :=
  fun _ _ h => loewySequence_le U₀ h_semi _ _ h

-- 4. Strict Monotonicity Lemma
/-- The sequence grows strictly prior to exhaustion. -/
lemma loewySequence_strict_mono (h_semi : IsSemiArtinian U₀) (o : Ordinal.{u}) :
    loewySequence U₀ h_semi o ≠ ⊤ → 
    loewySequence U₀ h_semi o < loewySequence U₀ h_semi (o + 1) := by
  intro h_ne
  have h_succ : loewySequence U₀ h_semi (o + 1) = nextLoewy U₀ (loewySequence U₀ h_semi o) h_semi := by
    dsimp [loewySequence]
    rw [Ordinal.limitRecOn_add_one]
  rw [h_succ]
  have hz : ¬ IsZero (residual U₀ (loewySequence U₀ h_semi o)) :=
    not_isZero_residual_of_ne_top U₀ _ h_ne
  dsimp [nextLoewy]
  rw [dif_neg hz]
  let a := (h_semi (loewySequence U₀ h_semi o) hz).choose
  let i := (h_semi (loewySequence U₀ h_semi o) hz).choose_spec.choose
  have ha_simple := (h_semi (loewySequence U₀ h_semi o) hz).choose_spec.choose_spec.1
  have hi : Mono i := (h_semi (loewySequence U₀ h_semi o) hz).choose_spec.choose_spec.2
  exact lt_cellular U₀ _ a i hi ha_simple

-- 5. Cardinal Bounding Lemma
/-- Because `Subobject U₀` is small (WellPowered), a strictly increasing map 
    from Ordinal to Subobject cannot exist. The sequence must stabilize. -/
lemma loewySequence_stabilizes (h_semi : IsSemiArtinian U₀) :
    ∃ (Ω : Ordinal.{u}), loewySequence U₀ h_semi Ω = loewySequence U₀ h_semi (Ω + 1) := by
  have h_ev := Ordinal.eventuallyConst_of_monotone (loewySequence_mono U₀ h_semi)
  rw [Filter.eventuallyConst_atTop] at h_ev
  rcases h_ev with ⟨Ω, hΩ⟩
  refine ⟨Ω, ?_⟩
  have h_le : Ω ≤ Ω + 1 := le_self_add
  exact (hΩ (Ω + 1) h_le).symm

-- 6. Final Theorem (Replacing the Axiom)
/-- Stabilization forces exhaustion. -/
theorem loewy_length_exists (h_semi : IsSemiArtinian U₀) : 
    ∃ (Ω : Ordinal.{u}), loewySequence U₀ h_semi Ω = ⊤ := by
  obtain ⟨Ω, hΩ⟩ := loewySequence_stabilizes U₀ h_semi
  refine ⟨Ω, ?_⟩
  by_contra h_ne
  have h_lt := loewySequence_strict_mono U₀ h_semi Ω h_ne
  rw [hΩ] at h_lt
  exact lt_irrefl _ h_lt

#print axioms loewy_length_exists

