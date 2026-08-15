/-
Copyright (c) 2026 The TACG Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TACG Contributors
-/

import TACG.Definitions
import TACG.Derivations.Necessity.NecessityDirection
import TACG.Derivations.Sufficiency.InjectiveComponentOutputs
import TACG.Derivations.Sufficiency.InjectiveMappingForSufficiency

/-!
# Injective Necessary and Sufficient Condition (Corollary 3)

This file formalizes the injective version of the main theorem:
compositional generalization is equivalent to AS-IR (Aligned Structure-Injective
Representation). This is a corollary of the main theorem, showing that
injective representation (Definition 15) captures the same condition as
the combination of unambiguous and minimized representations.
-/

open TACG.Definitions
open TACG.Derivations.Necessity.NecessityDirection
open TACG.Derivations.Sufficiency.InjectiveComponentOutputs
open TACG.Derivations.Sufficiency.InjectiveMappingForSufficiency

namespace TACG.Discussion.InjectiveNecessaryAndSufficientCondition

/-- Corollary 3 (Injective Necessary and Sufficient Condition).
    A model provably enables compositional generalization iff it has AS-IR.
    Necessity: from compositional generalization we get AS-UMR, then from
    unambiguous + minimized we derive injective representation.
    Sufficiency: directly apply the injective mapping lemma. -/
theorem injective_necessary_and_sufficient_condition (M : Model) (train test : List Sample)
    (h_correct_train : correct_predictions M train)
    (h_seen : seen_inputs_condition M train test) :
    CompositionalGeneralization M train test ↔ AS_IR M train test := by
  constructor
  · -- Necessity: from compositional generalization to AS-IR.
    intro h_cg
    -- Obtain AS-UMR from the necessity lemma.
    have h_as_umr := necessity_direction M train test h_cg h_correct_train h_seen
    rcases h_as_umr with ⟨Z, h_struct, h_unamb_min⟩
    -- Construct AS-IR with the same reference model.
    use Z
    constructor
    · exact h_struct
    · intro c hc
      specialize h_unamb_min c hc
      obtain ⟨h_unamb, h_min⟩ := h_unamb_min
      -- Restrict structural alignment from full dataset to training only.
      have h_struct_train : StructuralAlignment M Z.model train := by
        unfold StructuralAlignment
        intro s hs
        specialize h_struct s (by simp [hs])
        exact h_struct
      -- Unambiguous + minimized implies injective by Lemma 6.
      exact injective_component_outputs M Z.model train c h_struct_train h_unamb h_min
  · -- Sufficiency: from AS-IR to compositional generalization.
    intro h_as_ir
    rcases h_as_ir with ⟨Z, h_struct, h_inj⟩
    -- Directly apply the sufficiency lemma for injective representation.
    exact injective_mapping_for_sufficiency Z h_struct h_inj

end TACG.Discussion.InjectiveNecessaryAndSufficientCondition
