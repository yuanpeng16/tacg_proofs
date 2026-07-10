import Mathlib.Data.Fintype.Card

/-- Lemma 5 (Cardinality Bound for Injective Mappings) from the paper.
    If a function from a finite type α to a finite type β is injective,
    then the cardinality of α is at most the cardinality of β.
    This lemma is used in the necessity proof to relate set sizes
    for injective mappings between hypothesis and reference values. -/
lemma cardinality_bound_for_injective_mappings {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
  (hinj : Function.Injective f) :
  Fintype.card α ≤ Fintype.card β := by
  -- Apply the standard library result: an injection implies cardinality inequality.
  exact Fintype.card_le_of_injective f hinj
