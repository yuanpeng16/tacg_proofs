import TACG.MinimalExample.MinimalExampleVerification

open TACG.MinimalExample.MinimalExampleVerification

namespace TACG.MinimalExample.UnambiguousRepresentationVerification

/-- Lemma 4 (Unambiguous Representation Verification) from the paper.
    For the minimal example task, under the minimized representation condition
    and correct training predictions, the hidden node h has an unambiguous
    representation with respect to the true intermediate value z on the training
    set: if two training samples have the same h value, then they have the same
    z value (i.e., no two distinct reference values share the same hypothesis
    value). -/
lemma unambiguous_representation_verification (M : ExampleModel) (h_min : M.IsMinimized)
    (h_correct : ∀ s ∈ train_set, M.out s = y s) :
    ∀ s₁ ∈ train_set, ∀ s₂ ∈ train_set, M.h s₁ = M.h s₂ → z s₁ = z s₂ := by
  intro s₁ hs₁ s₂ hs₂ h_eq
  have h1 := h_z_correspondence_train M h_min h_correct s₁ hs₁
  have h2 := h_z_correspondence_train M h_min h_correct s₂ hs₂
  cases h1 with
  | inl h1a =>
    cases h2 with
    | inl h2a => rw [h1a.2, h2a.2]
    | inr h2b => exact False.elim (h_a_neq_h_b M h_correct (h1a.1.symm.trans (h_eq.trans h2b.1)))
  | inr h1b =>
    cases h2 with
    | inl h2a => exact False.elim (
        h_a_neq_h_b M h_correct (h2a.1.symm.trans (h_eq.symm.trans h1b.1)))
    | inr h2b => rw [h1b.2, h2b.2]

end TACG.MinimalExample.UnambiguousRepresentationVerification
