/-
Copyright (c) 2026 The TACG Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TACG Contributors
-/

import Mathlib.Tactic.NormNum
import TACG.MinimalExample.UnambiguousRepresentationVerification

/-!
# Minimal Example Verification (Corollary 2)

This file proves Corollary 2 from the paper: for the minimal example,
minimized representation (Definition 9) together with training correctness
suffices for compositional generalization.

We reuse definitions from UnambiguousRepresentationVerification.lean and
add the minimized representation condition.
-/

open TACG.MinimalExample.UnambiguousRepresentationVerification
open Sample  -- allow direct use of a, b, c, ...

namespace TACG.MinimalExample.MinimalExampleVerification

/--
Minimized representation condition (Definition 9): the hidden node h takes
exactly two distinct values across all samples. This matches the true
intermediate value z which also takes two values {0,1}.
-/
def IsMinimized (M : ExampleModel) : Prop :=
  (Finset.image M.h Finset.univ).card = 2

-- Helper lemma: if a Finset contains three distinct elements, its cardinality is at least 3.
private lemma card_ge_three_of_three_distinct {α : Type*} {s : Finset α} {a b x : α}
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

-- Basic inequality needed: h(a) ≠ h(b) follows from training correctness.
private lemma h_a_neq_h_b {M : ExampleModel} (h_correct : ∀ s ∈ train_set, M.out s = y s) :
    M.h a ≠ M.h b := by
  intro h_eq
  have out_eq := M.out_depends a b ⟨h_eq, by simp only [x₃]⟩
  rw [h_correct a (by decide), h_correct b (by decide)] at out_eq
  simp only [y, z, x₁, x₂, x₃] at out_eq
  norm_num at out_eq

-- Under minimized representation, every sample's h is either h(a) or h(b).
private lemma h_range {M : ExampleModel} (h_min : IsMinimized M)
    (h_correct : ∀ s ∈ train_set, M.out s = y s) (s : Sample) :
    M.h s = M.h a ∨ M.h s = M.h b := by
  let S := Finset.image M.h Finset.univ
  have h_card : S.card = 2 := h_min
  have h_a_mem : M.h a ∈ S := Finset.mem_image_of_mem M.h (Finset.mem_univ a)
  have h_b_mem : M.h b ∈ S := Finset.mem_image_of_mem M.h (Finset.mem_univ b)
  have h_s_mem : M.h s ∈ S := Finset.mem_image_of_mem M.h (Finset.mem_univ s)
  have h_ab_ne := h_a_neq_h_b (M := M) h_correct
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

-- Using unambiguous representation (Lemma 4) to pin down h(c) and h(d).
private lemma h_c_eq_b {M : ExampleModel} (h_min : IsMinimized M)
    (h_correct : ∀ s ∈ train_set, M.out s = y s) :
    M.h c = M.h b := by
  rcases h_range h_min h_correct c with hc_a | hc_b
  · have h_uniq := unambiguous_representation_verification M h_correct
    have h_z_eq := h_uniq c (by decide) a (by decide) hc_a
    simp only [z, x₁, x₂] at h_z_eq
    norm_num at h_z_eq
  · exact hc_b

private lemma h_d_eq_a {M : ExampleModel} (h_min : IsMinimized M)
    (h_correct : ∀ s ∈ train_set, M.out s = y s) :
    M.h d = M.h a := by
  rcases h_range h_min h_correct d with hd_a | hd_b
  · exact hd_a
  · have h_uniq := unambiguous_representation_verification M h_correct
    have h_z_eq := h_uniq d (by decide) b (by decide) hd_b
    simp only [z, x₁, x₂] at h_z_eq
    norm_num at h_z_eq

-- By determinism of h, test samples g and h have the same h as c and d respectively.
private lemma h_g_eq_c {M : ExampleModel} : M.h g = M.h c :=
  M.h_depends g c (by simp [x₁, x₂])

private lemma h_h_eq_d {M : ExampleModel} : M.h h = M.h d :=
  M.h_depends h d (by simp [x₁, x₂])

-- Test correctness for g and h.
private lemma test_g_correct {M : ExampleModel} (h_min : IsMinimized M)
    (h_correct : ∀ s ∈ train_set, M.out s = y s) :
    M.out g = y g := by
  have h_eq : M.h g = M.h b := by
    rw [h_g_eq_c, h_c_eq_b h_min h_correct]
  have x3_eq : x₃ g = x₃ b := by simp only [x₃]
  have out_eq := M.out_depends g b ⟨h_eq, x3_eq⟩
  rw [out_eq, h_correct b (by decide)]
  rfl

private lemma test_h_correct {M : ExampleModel} (h_min : IsMinimized M)
    (h_correct : ∀ s ∈ train_set, M.out s = y s) :
    M.out h = y h := by
  have h_eq : M.h h = M.h a := by
    rw [h_h_eq_d, h_d_eq_a h_min h_correct]
  have x3_eq : x₃ h = x₃ a := by simp only [x₃]
  have out_eq := M.out_depends h a ⟨h_eq, x3_eq⟩
  rw [out_eq, h_correct a (by decide)]
  rfl

/-- Corollary 2: Minimal Example Verification.
    If the model is correct on training and has minimized representation,
    then it is correct on all test samples. -/
theorem minimal_example_verification (M : ExampleModel) (h_min : IsMinimized M) :
    (∀ s ∈ train_set, M.out s = y s) → ∀ s ∈ test_set, M.out s = y s := by
  intro h_correct s hs
  simp only [test_set, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with (rfl | rfl)
  · exact test_g_correct h_min h_correct
  · exact test_h_correct h_min h_correct

end TACG.MinimalExample.MinimalExampleVerification
