import Mathlib.Data.Fintype.Card

open Finset
open Function

namespace TACG.Derivations.MathematicalPreliminaries.MappingsOnNodes

/-- Lemma 1 (Mappings on Nodes) from the paper.
    For finite sets S₁ (hypothesis representations) and S₂ (reference representations),
    given a well-defined and surjective mapping f : S₁ → S₂,
    f is injective iff |S₁| = |S₂|, i.e., the domain size is minimized. -/
lemma mappings_on_nodes {S₁ S₂ : Type} [Fintype S₁] [Fintype S₂] (f : S₁ → S₂)
    (hf_surj : Surjective f) :
    Injective f ↔ Fintype.card S₁ = Fintype.card S₂ := by
  classical
  constructor
  · -- Direction: injective → equal cardinalities
    intro h_inj
    have h_le : Fintype.card S₁ ≤ Fintype.card S₂ :=
      Fintype.card_le_of_injective f h_inj
    have h_ge : Fintype.card S₂ ≤ Fintype.card S₁ :=
      Fintype.card_le_of_surjective f hf_surj
    exact Nat.le_antisymm h_le h_ge
  · -- Direction: equal cardinalities → injective
    -- We prove the contrapositive via a deletion argument.
    intro h_card_eq
    by_contra h_not_inj
    rcases not_injective_iff.mp h_not_inj with ⟨x, y, h_eq, h_ne⟩
    -- Construct a new surjective mapping by removing x from the domain.
    -- Since y (which is distinct from x) still maps to f(x), surjectivity is preserved.
    have surj_erase : Surjective (fun (z : {z : S₁ // z ≠ x}) => f z.val) := by
      intro b
      rcases hf_surj b with ⟨a, ha⟩
      by_cases hax : a = x
      · refine ⟨⟨y, h_ne.symm⟩, ?_⟩
        rw [← ha, hax, h_eq]
      · exact ⟨⟨a, hax⟩, ha⟩
    -- The subtype {z | z ≠ x} has cardinality strictly less than S₁.
    have card_subtype_lt : Fintype.card {z : S₁ // z ≠ x} < Fintype.card S₁ := by
      rw [Fintype.card_subtype]
      have hx : x ∈ (univ : Finset S₁) := mem_univ x
      have h_filter_ssubset : (filter (· ≠ x) univ) ⊂ univ := by
        refine ⟨filter_subset _ _, fun h => ?_⟩
        have : x ∉ filter (· ≠ x) univ := by simp
        exact this (h hx)
      exact Finset.card_lt_card h_filter_ssubset
    -- Surjectivity gives an upper bound on cardinality.
    have h_card_le : Fintype.card S₂ ≤ Fintype.card {z : S₁ // z ≠ x} :=
      Fintype.card_le_of_surjective _ surj_erase
    -- Combine to obtain a contradiction with h_card_eq.
    have h_lt : Fintype.card S₂ < Fintype.card S₁ :=
      lt_of_le_of_lt h_card_le card_subtype_lt
    rw [h_card_eq] at h_lt
    exact lt_irrefl _ h_lt

end TACG.Derivations.MathematicalPreliminaries.MappingsOnNodes
