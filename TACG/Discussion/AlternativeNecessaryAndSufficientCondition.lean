/-
Copyright (c) 2026 The TACG Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TACG Contributors
-/

import TACG.Definitions
import TACG.Derivations.Necessity.NecessityDirection
import TACG.Derivations.Sufficiency.SufficiencyDirection
import TACG.Discussion.SeenTestComponentInputs

/-!
# Theorem 2 (Alternative Necessary and Sufficient Condition)

This file formalizes the alternative version of the main theorem,
where the "seen test inputs" requirement is part of the definition
of compositional generalization itself (Definition 14 in the paper),
rather than a separate assumption.
-/

open TACG.Definitions
open TACG.Derivations.Necessity.NecessityDirection
open TACG.Derivations.Sufficiency.SufficiencyDirection
open TACG.Discussion.SeenTestComponentInputs

namespace TACG.Discussion.AlternativeNecessaryAndSufficientCondition

/-- Theorem 2 (Alternative Necessary and Sufficient Condition).
    A model enables alternative compositional generalization iff it has AS-UMR.
    Unlike Theorem 1, this version does not require a separate seen-inputs
    assumption because that condition is built into the definition of
    AlternativeCompositionalGeneralization. -/
theorem alternative_necessary_and_sufficient_condition (M : Model) (train test : List Sample)
    (h_correct_train : correct_predictions M train) :
    AlternativeCompositionalGeneralization M train test ↔ AS_UMR M train test := by
  constructor
  · -- Necessity: from alternative compositional generalization to AS-UMR.
    intro h_alt
    have h_cg := h_alt.1          -- CompositionalGeneralization
    have h_seen := h_alt.2        -- seen_inputs_condition
    exact necessity_direction M train test h_cg h_correct_train h_seen
  · -- Sufficiency: from AS-UMR to alternative compositional generalization.
    intro h_as_umr
    -- First prove the original compositional generalization.
    have h_cg := sufficiency_direction M train test h_as_umr
    -- Then prove that all test component inputs are seen in training.
    rcases h_as_umr with ⟨Z, h_struct, h_cond⟩
    have h_seen := seen_test_component_inputs Z M h_struct
      (fun c hc => (h_cond c hc).1)   -- unambiguous representation
      (fun c hc => (h_cond c hc).2)   -- minimized representation
    exact ⟨h_cg, h_seen⟩

end TACG.Discussion.AlternativeNecessaryAndSufficientCondition
