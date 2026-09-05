import Mathlib.Data.Fintype.Card

/-!
# Unambiguous Representation Verification (Lemma 4)

This file formalizes the minimal example and proves Lemma 4 from the paper:
unambiguous representation does not require minimized representation.
It shows that for the three‑input XOR task, if the model is correct on training,
then the hidden node `h` is a function of the true intermediate value `z` on
the training set: `h(s₁) = h(s₂)` implies `z(s₁) = z(s₂)`.
-/

open Finset

namespace TACG.MinimalExample.UnambiguousRepresentationVerification

/-- The eight samples of the minimal example, as in Table 1 of the paper. -/
inductive Sample : Type where
  | a | b | c | d | e | f | g | h
deriving DecidableEq

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
(computed from h and x₃). The model is deterministic.
-/
structure ExampleModel where
  h : Sample → Nat
  out : Sample → Nat
  -- Determinism of the first component: h depends only on (x₁,x₂).
  h_depends : ∀ s₁ s₂, x₁ s₁ = x₁ s₂ ∧ x₂ s₁ = x₂ s₂ → h s₁ = h s₂
  -- Determinism of the second component: out depends only on (h,x₃).
  out_depends : ∀ s₁ s₂, h s₁ = h s₂ ∧ x₃ s₁ = x₃ s₂ → out s₁ = out s₂

/-- Lemma 4: Unambiguous Representation Verification.
    It does **not** require the minimized representation condition. -/
lemma unambiguous_representation_verification (M : ExampleModel)
    (h_correct : ∀ s ∈ train_set, M.out s = y s) :
    ∀ s₁ ∈ train_set, ∀ s₂ ∈ train_set, M.h s₁ = M.h s₂ → z s₁ = z s₂ := by
  -- Basic deterministic equalities (from h_depends)
  have h_ae : M.h a = M.h e := M.h_depends a e (by simp [x₁, x₂])
  have h_bf : M.h b = M.h f := M.h_depends b f (by simp [x₁, x₂])
  -- Inequalities derived from training correctness
  have h_ab : M.h a ≠ M.h b := by
    intro h_eq
    have out_eq := M.out_depends a b ⟨h_eq, rfl⟩
    rw [h_correct a (by decide), h_correct b (by decide)] at out_eq
    simp [y, z, x₁, x₂, x₃] at out_eq
  have h_cd : M.h c ≠ M.h d := by
    intro h_eq
    have out_eq := M.out_depends c d ⟨h_eq, rfl⟩
    rw [h_correct c (by decide), h_correct d (by decide)] at out_eq
    simp [y, z, x₁, x₂, x₃] at out_eq
  have h_ce : M.h c ≠ M.h e := by
    intro h_eq
    have out_eq := M.out_depends c e ⟨h_eq, rfl⟩
    rw [h_correct c (by decide), h_correct e (by decide)] at out_eq
    simp [y, z, x₁, x₂, x₃] at out_eq
  have h_df : M.h d ≠ M.h f := by
    intro h_eq
    have out_eq := M.out_depends d f ⟨h_eq, rfl⟩
    rw [h_correct d (by decide), h_correct f (by decide)] at out_eq
    simp [y, z, x₁, x₂, x₃] at out_eq
  have h_ef : M.h e ≠ M.h f := by
    intro h_eq
    have out_eq := M.out_depends e f ⟨h_eq, rfl⟩
    rw [h_correct e (by decide), h_correct f (by decide)] at out_eq
    simp [y, z, x₁, x₂, x₃] at out_eq
  -- Derive cross‑group inequalities (z=0 group: {a,d,e}, z=1 group: {b,c,f})
  have h_ac : M.h a ≠ M.h c := by
    rw [h_ae]          -- goal: M.h e ≠ M.h c
    exact h_ce.symm    -- h_ce.symm : M.h e ≠ M.h c
  have h_af : M.h a ≠ M.h f := by
    rw [h_ae]          -- goal: M.h e ≠ M.h f
    exact h_ef         -- h_ef : M.h e ≠ M.h f
  have h_db : M.h d ≠ M.h b := by
    rw [h_bf]          -- goal: M.h d ≠ M.h f
    exact h_df
  have h_eb : M.h e ≠ M.h b := by
    rw [h_bf]          -- goal: M.h e ≠ M.h f
    exact h_ef
  have h_ec : M.h e ≠ M.h c := h_ce.symm
  have h_dc : M.h d ≠ M.h c := h_cd.symm
  -- Now prove the main implication.
  intros s1 hs1 s2 hs2 heq
  by_contra hz_neq
  -- We classify samples into two groups based on z.
  let group0 : Finset Sample := {a, d, e}
  let group1 : Finset Sample := {b, c, f}
  -- Show that every training sample is in exactly one group and its z value matches.
  have mem_group : ∀ s ∈ train_set, (s ∈ group0 ∧ z s = 0) ∨ (s ∈ group1 ∧ z s = 1) := by
    intro s hs
    simp only [train_set, mem_insert, mem_singleton] at hs
    rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl)
    · left; simp [group0, z, x₁, x₂]
    · right; simp [group1, z, x₁, x₂]
    · right; simp [group1, z, x₁, x₂]
    · left; simp [group0, z, x₁, x₂]
    · left; simp [group0, z, x₁, x₂]
    · right; simp [group1, z, x₁, x₂]
  -- Cross inequality for all group0 vs group1 pairs.
  have cross_ineq : ∀ s ∈ group0, ∀ t ∈ group1, M.h s ≠ M.h t := by
    intro s hs t ht
    simp only [group0, group1, mem_insert, mem_singleton] at hs ht
    rcases hs with (rfl | rfl | rfl) <;> rcases ht with (rfl | rfl | rfl)
    · exact h_ab
    · exact h_ac
    · exact h_af
    · exact h_db
    · exact h_dc
    · exact h_df
    · exact h_eb
    · exact h_ec
    · exact h_ef
  -- Apply the classification to s1 and s2 using explicit cases to avoid variable name conflicts.
  cases mem_group s1 hs1 with
  | inl h1 =>
    cases mem_group s2 hs2 with
    | inl h2 =>
      -- both group0 -> z equal, contradiction
      have : z s1 = z s2 := by rw [h1.2, h2.2]
      contradiction
    | inr h2 =>
      -- s1 group0, s2 group1
      exact cross_ineq s1 h1.1 s2 h2.1 heq
  | inr h1 =>
    cases mem_group s2 hs2 with
    | inl h2 =>
      -- s1 group1, s2 group0
      have h_sym := cross_ineq s2 h2.1 s1 h1.1
      exact h_sym heq.symm
    | inr h2 =>
      -- both group1 -> z equal, contradiction
      have : z s1 = z s2 := by rw [h1.2, h2.2]
      contradiction

end TACG.MinimalExample.UnambiguousRepresentationVerification
