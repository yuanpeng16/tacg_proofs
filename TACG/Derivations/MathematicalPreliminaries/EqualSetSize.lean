import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

open Finset
open Function

namespace TACG.Derivations.MathematicalPreliminaries.EqualSetSize

/-- Lemma 7 (Equal Set Size) from the paper.
    For a surjective function between finite types, injectivity is equivalent to
    equal cardinalities. This is the key lemma used to prove Lemma 1
    (Mappings on Nodes): minimizing the domain size of a well-defined surjective
    mapping makes it injective. -/
lemma equal_set_size {α β : Type} [Fintype α] [Fintype β] (f : α → β)
  (h_surj : Function.Surjective f) :
  Function.Injective f ↔ Fintype.card α = Fintype.card β :=
by
  classical
  constructor
  · -- Direction: injective → equal cardinalities
    intro h_inj
    have h_le : Fintype.card α ≤ Fintype.card β :=
      Fintype.card_le_of_injective f h_inj
    have h_ge : Fintype.card β ≤ Fintype.card α :=
      Fintype.card_le_of_surjective f h_surj
    exact Nat.le_antisymm h_le h_ge
  · -- Direction: equal cardinalities → injective
    intro h_card_eq
    by_contra h_not_inj
    rcases not_injective_iff.mp h_not_inj with ⟨x, y, h_eq, h_ne⟩
    -- Lemma 1: after removing x, the restricted f is still surjective
    have surj_erase : Surjective (fun (z : {z : α // z ≠ x}) => f z.val) := by
      intro b
      rcases h_surj b with ⟨a, ha⟩
      by_cases hax : a = x
      · refine ⟨⟨y, h_ne.symm⟩, ?_⟩
        rw [← ha, hax, h_eq]
      · exact ⟨⟨a, hax⟩, ha⟩
    -- Lemma 2: the subtype {z | z ≠ x} has cardinality strictly less than α
    have card_subtype_lt : Fintype.card {z : α // z ≠ x} < Fintype.card α := by
      rw [Fintype.card_subtype]
      have hx : x ∈ (univ : Finset α) := mem_univ x
      have h_filter_ssubset : (filter (· ≠ x) univ) ⊂ univ := by
        refine ⟨filter_subset _ _, fun h => ?_⟩
        have : x ∉ filter (· ≠ x) univ := by simp
        exact this (h hx)
      exact Finset.card_lt_card h_filter_ssubset
    -- Lemma 3: surjectivity gives an upper bound on cardinality
    have h_card_le : Fintype.card β ≤ Fintype.card {z : α // z ≠ x} :=
      Fintype.card_le_of_surjective _ surj_erase
    -- Combine to obtain a contradiction
    have h_lt : Fintype.card β < Fintype.card α :=
      lt_of_le_of_lt h_card_le card_subtype_lt
    rw [h_card_eq] at h_lt
    exact lt_irrefl _ h_lt

end TACG.Derivations.MathematicalPreliminaries.EqualSetSize
