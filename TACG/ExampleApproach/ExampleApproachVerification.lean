/-
Copyright (c) 2026 The TACG Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TACG Contributors
-/

import TACG.Definitions
import TACG.ExampleApproach.MinimumEntropyImpliesMinimizedRepresentation
import TACG.Derivations.Sufficiency.SufficiencyDirection

/-!
# Corollary 1: Example Approach Verification

This file formalizes Corollary 1 from the paper:
If the minimum entropy is achieved for all non-output components,
then a model trained according to Algorithm 1 enables correct test prediction.

The proof proceeds as follows:
1. From structural alignment, unambiguous representation, and minimum entropy,
   we derive the minimized representation condition (via Lemma 3).
2. Together these form AS-UMR.
3. By Proposition 2 (sufficiency), AS-UMR implies compositional generalization.
4. Combining with correct training predictions yields correct test predictions.
-/

open TACG.Definitions
open TACG.ExampleApproach.MinimumEntropyImpliesMinimizedRepresentation
open TACG.Derivations.Sufficiency.SufficiencyDirection

namespace TACG.ExampleApproach.ExampleApproachVerification

/-- Corollary 1: If minimum entropy is achieved for all components,
    a model trained according to Algorithm 1 provably enables correct test prediction. -/
lemma example_approach_verification (M : Model) (train test : List Sample)
    (Z : ReferenceModel train test)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (h_unambig : ∀ c ∈ components_list M train, UnambiguousRepresentation c train M Z.model)
    (h_min_entropy : ∀ c ∈ components_list M train,
       let D := ξ_set M train c
       ∃ p : Value → ℝ, (∀ h, h ∈ D ↔ p h > 0) ∧ (∑ h ∈ D, p h = 1) ∧ IsMinimalEntropy D p)
    (h_train_correct : correct_predictions M train) :
    correct_predictions M test :=
by
  -- 1. Establish AS-UMR from the given conditions: structural alignment from
  --    h_struct, unambiguous from h_unambig, and minimized from minimum entropy
  --    via Lemma 3 (minimum entropy implies minimized representation).
  have h_as_umr : AS_UMR M train test := by
    unfold AS_UMR
    use Z
    constructor
    · exact h_struct
    · intros c hc
      constructor
      · exact h_unambig c hc
      · specialize h_min_entropy c hc
        obtain ⟨p, h_support, h_sum, h_min⟩ := h_min_entropy
        -- Restrict structural alignment from full dataset to training samples.
        have h_struct_train : StructuralAlignment M Z.model train := by
          unfold StructuralAlignment at h_struct ⊢
          intros s hs
          exact h_struct s (by simp [hs])
        -- Lemma 3: minimum entropy on a component implies minimized representation
        -- (Definition 9) given structural alignment and unambiguous representation.
        exact minimum_entropy_implies_minimized_representation
                M Z.model train c h_struct_train (h_unambig c hc) p h_support h_sum h_min
  -- 2. Apply sufficiency direction (Proposition 2) to obtain compositional
  --    generalization: AS-UMR implies CompositionalGeneralization M train test.
  have h_cg := sufficiency_direction M train test h_as_umr
  -- 3. Combine with correct training predictions to get correct test predictions.
  exact h_cg h_train_correct

end TACG.ExampleApproach.ExampleApproachVerification
