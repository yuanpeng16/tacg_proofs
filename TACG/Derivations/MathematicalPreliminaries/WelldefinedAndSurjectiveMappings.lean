import Mathlib.Data.Fintype.Card

open Fintype

/-- Lemma 6 (Well-defined and Surjective Mappings) from the paper.
    For finite types S1 and S2, if f : S1 → S2 is surjective, then |S1| ≥ |S2|.
    This is used in the necessity proof to establish that a well-defined and
    surjective mapping has domain size at least the codomain size,
    complementing the injectivity bound. -/
lemma welldefined_and_surjective_mappings {S1 S2 : Type} [Fintype S1] [Fintype S2]
    (f : S1 -> S2) (hf : Function.Surjective f) :
    card S2 <= card S1 :=
  card_le_of_surjective f hf
