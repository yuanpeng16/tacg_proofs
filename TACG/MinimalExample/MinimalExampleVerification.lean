/-
Copyright (c) 2026 The TACG Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TACG Contributors
-/

import Mathlib.Data.Fintype.Card

/-!
# Minimal Example Verification (Corollary 2)

This file formalizes the minimal example from Section 5 of the paper.
It defines the three-input XOR task, the training/test split, and proves that
if the model satisfies the minimized representation condition (i.e., the hidden
node h takes exactly two distinct values on all samples), then the model
correctly predicts the test samples g and h.

The proof follows the paper's reasoning:
1. From minimized representation, the hidden value h(s) for each training sample
   is forced to be either h(a) or h(b).
2. Using training correctness and determinism, we derive the correspondence:
   h(s) = h(a) iff z(s) = 0, and h(s) = h(b) iff z(s) = 1.
3. By determinism, test samples g and h map to c and d respectively,
   yielding the correct test outputs.
-/

open Finset

namespace TACG.MinimalExample.MinimalExampleVerification

/-- The eight samples of the minimal example, as in Table 1 of the paper. -/
inductive Sample : Type where
  | a | b | c | d | e | f | g | h
deriving DecidableEq

-- Open the namespace to make constructors a, b, ... directly available.
open Sample

-- Manual Fintype instance for Sample.
instance : Fintype Sample where
  elems := {a, b, c, d, e, f, g, h}
  complete := by
    intro x
    cases x <;> simp

/-- Input x₁ for each sample. -/
def x₁ : Sample → Nat
  | a => 0 | b => 0 | c => 1 | d => 1 | e => 0 | f => 0 | g => 1 | h => 1

/-- Input x₂ for each sample. -/
def x₂ : Sample → Nat
  | a => 0 | b => 1 | c => 0 | d => 1 | e => 0 | f => 1 | g => 0 | h => 1

/-- Input x₃ for each sample. -/
def x₃ : Sample → Nat
  | a => 0 | b => 0 | c => 1 | d => 1 | e => 1 | f => 1 | g => 0 | h => 0

/-- True intermediate value z = x₁ xor x₂. -/
def z (s : Sample) : Nat := Nat.xor (x₁ s) (x₂ s)

/-- True output y = z xor x₃. -/
def y (s : Sample) : Nat := Nat.xor (z s) (x₃ s)

/-- Training set contains samples a through f (six samples). -/
def train_set : Finset Sample := {a, b, c, d, e, f}

/-- Test set contains samples g and h (unseen combinations). -/
def test_set : Finset Sample := {g, h}

/--
ExampleModel: a simple two-layer model corresponding to Algorithm 4.
It has a hidden node h (computed from x₁,x₂) and an output node out
(computed from h and x₃). The model is deterministic and correct on training.
-/
structure ExampleModel where
  h : Sample → Nat
  out : Sample → Nat
  -- Determinism of the first component: h depends only on (x₁,x₂).
  h_depends : ∀ s₁ s₂, x₁ s₁ = x₁ s₂ ∧ x₂ s₁ = x₂ s₂ → h s₁ = h s₂
  -- Determinism of the second component: out depends only on (h,x₃).
  out_depends : ∀ s₁ s₂, h s₁ = h s₂ ∧ x₃ s₁ = x₃ s₂ → out s₁ = out s₂
  -- Correct training predictions (Definition 5 antecedent).
  correct_train : ∀ s, s ∈ train_set → out s = y s

/--
Minimized representation condition (Definition 9): the hidden node h takes
exactly two distinct values across all samples. This matches the true
intermediate value z which also takes two values {0,1}.
-/
def ExampleModel.IsMinimized (M : ExampleModel) : Prop :=
  (Finset.image M.h Finset.univ).card = 2

/-- Helper: if a Finset contains three distinct elements, its cardinality is at least 3. -/
private lemma card_ge_three_of_three_distinct {α : Type _} {s : Finset α} {a b x : α}
    (ha : a ∈ s) (hb : b ∈ s) (hx : x ∈ s) (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x) :
    3 ≤ s.card := by
  classical
    by_contra h_not
    push Not at h_not
    have h_card_le_2 : s.card ≤ 2 := by omega
    have h_erase_a_card : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
    have h_erase_b_card : ((s.erase a).erase b).card = (s.erase a).card - 1 := by
      apply Finset.card_erase_of_mem
      rw [Finset.mem_erase]
      exact ⟨Ne.symm hab, hb⟩
    have hx_mem : x ∈ (s.erase a).erase b := by
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨Ne.symm hbx, Ne.symm hax, hx⟩
    have h_card_pos : 0 < ((s.erase a).erase b).card := Finset.card_pos.mpr ⟨x, hx_mem⟩
    have h_sub2 : ((s.erase a).erase b).card = s.card - 2 := by
      rw [h_erase_b_card, h_erase_a_card]; omega
    have h_bad : 0 < s.card - 2 := by rw [←h_sub2]; exact h_card_pos
    omega

-- 1. Unambiguous representation relies on several inequality pairs within training.

/-- In a correct model, h(a) ≠ h(b) because otherwise outputs a and b would be equal. -/
lemma h_a_neq_h_b (M : ExampleModel) : M.h a ≠ M.h b := by
  intro h_eq
  have out_eq := M.out_depends a b ⟨h_eq, rfl⟩
  rw [M.correct_train a (by decide), M.correct_train b (by decide)] at out_eq
  simp [y, z, x₁, x₂, x₃] at out_eq

/-- Similarly, h(c) ≠ h(d). -/
private lemma h_c_neq_h_d (M : ExampleModel) : M.h c ≠ M.h d := by
  intro h_eq
  have out_eq := M.out_depends c d ⟨h_eq, rfl⟩
  rw [M.correct_train c (by decide), M.correct_train d (by decide)] at out_eq
  simp [y, z, x₁, x₂, x₃] at out_eq

/-- Under minimized representation, the image of h has exactly two values,
    so every sample's h is either h(a) or h(b). -/
private lemma h_range (M : ExampleModel) (h_min : M.IsMinimized) (s : Sample) :
    M.h s = M.h a ∨ M.h s = M.h b := by
  let S := Finset.image M.h Finset.univ
  have h_card : S.card = 2 := h_min
  have h_a_mem : M.h a ∈ S := Finset.mem_image_of_mem M.h (Finset.mem_univ a)
  have h_b_mem : M.h b ∈ S := Finset.mem_image_of_mem M.h (Finset.mem_univ b)
  have h_s_mem : M.h s ∈ S := Finset.mem_image_of_mem M.h (Finset.mem_univ s)
  have h_ab_ne : M.h a ≠ M.h b := h_a_neq_h_b M
  by_cases ha_eq : M.h s = M.h a
  · left; exact ha_eq
  · by_cases hb_eq : M.h s = M.h b
    · right; exact hb_eq
    · exfalso
      have hax' : M.h a ≠ M.h s := by simpa using Ne.symm (show ¬ M.h s = M.h a from ha_eq)
      have hbx' : M.h b ≠ M.h s := by simpa using Ne.symm (show ¬ M.h s = M.h b from hb_eq)
      have h_ge3 : 3 ≤ S.card := card_ge_three_of_three_distinct
        h_a_mem h_b_mem h_s_mem h_ab_ne hax' hbx'
      rw [h_card] at h_ge3
      exact Nat.not_succ_le_self 2 h_ge3

/-- From determinism and minimized representation, derive the mapping for training samples. -/
private lemma h_c_eq_b (M : ExampleModel) (h_min : M.IsMinimized) :
    M.h c = M.h b := by
  have h_ae : M.h a = M.h e := M.h_depends a e (by simp [x₁, x₂])
  have h_ce : M.h c ≠ M.h e := by
    intro h_eq
    have out_eq := M.out_depends c e ⟨h_eq, rfl⟩
    rw [M.correct_train c (by decide), M.correct_train e (by decide)] at out_eq
    simp [y, z, x₁, x₂, x₃] at out_eq
  have h_c_ne_a : M.h c ≠ M.h a := by
    intro h_eq
    apply h_ce
    rw [← h_ae, h_eq]
  cases h_range M h_min c with
  | inl hc => exact False.elim (h_c_ne_a hc)
  | inr hc => exact hc

private lemma h_d_eq_a (M : ExampleModel) (h_min : M.IsMinimized) :
    M.h d = M.h a := by
  have h_c_eq_b := h_c_eq_b M h_min
  have h_db : M.h d ≠ M.h b := by
    intro h_eq
    have h_eq_dc : M.h d = M.h c := by
      rw [h_eq, h_c_eq_b]
    exact h_c_neq_h_d M h_eq_dc.symm
  cases h_range M h_min d with
  | inl hd => exact hd
  | inr hd => exact False.elim (h_db hd)

-- 2. Unambiguous representation on training: h same ⇒ z same.
-- The paper proves this as Lemma 4 (Unambiguous Representation Verification).
lemma h_z_correspondence_train (M : ExampleModel) (h_min : M.IsMinimized)
    (s : Sample) (hs : s ∈ train_set) :
    (M.h s = M.h a ∧ z s = 0) ∨ (M.h s = M.h b ∧ z s = 1) := by
  have h_ae : M.h a = M.h e := M.h_depends a e (by simp [x₁, x₂])
  have h_bf : M.h b = M.h f := M.h_depends b f (by simp [x₁, x₂])
  have h_c_eq_b := h_c_eq_b M h_min
  have h_d_eq_a := h_d_eq_a M h_min
  cases s with
  | a => left; exact ⟨rfl, rfl⟩
  | b => right; exact ⟨rfl, rfl⟩
  | c => right; exact ⟨h_c_eq_b, rfl⟩
  | d => left; exact ⟨h_d_eq_a, rfl⟩
  | e => left; exact ⟨h_ae.symm, rfl⟩
  | f => right; exact ⟨h_bf.symm, rfl⟩
  | g => exfalso; simp [train_set] at hs
  | h => exfalso; simp [train_set] at hs

-- 3. Minimized + unambig ⇒ bijection on training: z same ⇒ h same.
private lemma h_inj_wrt_z_train (M : ExampleModel) (h_min : M.IsMinimized) :
    ∀ s₁ ∈ train_set, ∀ s₂ ∈ train_set, z s₁ = z s₂ → M.h s₁ = M.h s₂ := by
  intro s₁ hs₁ s₂ hs₂ hz_eq
  have h_eq_a_iff_z_0 : ∀ s ∈ train_set, (M.h s = M.h a ↔ z s = 0) := by
    intro s hs
    constructor
    · intro h
      have hz := h_z_correspondence_train M h_min s hs
      cases hz with
      | inl hz0 => exact hz0.2
      | inr hz1 => exact False.elim (h_a_neq_h_b M (h.symm.trans hz1.1))
    · intro hz0
      have hz := h_z_correspondence_train M h_min s hs
      cases hz with
      | inl hz1 => exact hz1.1
      | inr hz1 => exact absurd hz0 (by simp [hz1.2])
  have h_eq_b_iff_z_1 : ∀ s ∈ train_set, (M.h s = M.h b ↔ z s = 1) := by
    intro s hs
    constructor
    · intro h
      have hz := h_z_correspondence_train M h_min s hs
      cases hz with
      | inl hz0 => exact False.elim (h_a_neq_h_b M (hz0.1.symm.trans h))
      | inr hz1 => exact hz1.2
    · intro hz1
      have hz := h_z_correspondence_train M h_min s hs
      cases hz with
      | inl hz0 => exact absurd hz1 (by simp [hz0.2])
      | inr hz1' => exact hz1'.1
  by_cases z_eq_0 : z s₁ = 0
  · rw [z_eq_0] at hz_eq
    have h1 := (h_eq_a_iff_z_0 s₁ hs₁).mpr z_eq_0
    have h2 := (h_eq_a_iff_z_0 s₂ hs₂).mpr hz_eq.symm
    exact h1.trans h2.symm
  · have hz1 := h_z_correspondence_train M h_min s₁ hs₁
    cases hz1 with
    | inl hz0 => exact absurd hz0.2 z_eq_0
    | inr hz1' =>
      have z_eq_1 : z s₁ = 1 := hz1'.2
      rw [z_eq_1] at hz_eq
      have h1 := (h_eq_b_iff_z_1 s₁ hs₁).mpr z_eq_1
      have h2 := (h_eq_b_iff_z_1 s₂ hs₂).mpr hz_eq.symm
      exact h1.trans h2.symm

-- 4. By determinism, test samples g and h map to c and d respectively,
--    then use the bijection to get their h values.
private lemma h_g_eq_b (M : ExampleModel) (h_min : M.IsMinimized) :
    M.h g = M.h b := by
  have h_g_eq_c : M.h g = M.h c := M.h_depends g c (by simp [x₁, x₂])
  rw [h_g_eq_c]
  exact h_inj_wrt_z_train M h_min c (by decide) b (by decide) (by simp [z, x₁, x₂])

private lemma h_h_eq_a (M : ExampleModel) (h_min : M.IsMinimized) :
    M.h h = M.h a := by
  have h_h_eq_d : M.h h = M.h d := M.h_depends h d (by simp [x₁, x₂])
  rw [h_h_eq_d]
  exact h_inj_wrt_z_train M h_min d (by decide) a (by decide) (by simp [z, x₁, x₂])

-- 5. Test correctness via out_depends and training correctness.
private lemma test_g_correct (M : ExampleModel) (h_min : M.IsMinimized) :
    M.out g = y g := by
  have h_eq : M.h g = M.h b := h_g_eq_b M h_min
  have x3_eq : x₃ g = x₃ b := by simp [x₃]
  have out_eq := M.out_depends g b ⟨h_eq, x3_eq⟩
  rw [out_eq, M.correct_train b (by decide)]
  rfl   -- y b = y g (definitionally equal)

private lemma test_h_correct (M : ExampleModel) (h_min : M.IsMinimized) :
    M.out h = y h := by
  have h_eq : M.h h = M.h a := h_h_eq_a M h_min
  have x3_eq : x₃ h = x₃ a := by simp [x₃]
  have out_eq := M.out_depends h a ⟨h_eq, x3_eq⟩
  rw [out_eq, M.correct_train a (by decide)]
  rfl   -- y a = y h (definitionally equal)

/-!
# Corollary 2: Minimal Example Verification

This theorem formalizes Corollary 2 from the paper:
In the minimal example task, if the minimum entropy (equivalently, minimized
representation) is achieved for the hidden node, then the model correctly
predicts the test samples g and h.
-/
theorem minimal_example_verification (M : ExampleModel) (h_min : M.IsMinimized) :
    ∀ s ∈ test_set, M.out s = y s := by
  intro s hs
  simp only [test_set, mem_insert, mem_singleton] at hs
  cases hs
  · subst s
    exact test_g_correct M h_min
  · subst s
    exact test_h_correct M h_min

end TACG.MinimalExample.MinimalExampleVerification
