/-
Copyright (c) 2026 The TACG Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TACG Contributors
-/

import TACG.Derivations.Necessity.NecessityDirection
import TACG.Derivations.Sufficiency.SufficiencyDirection

/-!
# Formalization of Theorem 1 (Necessary and Sufficient Condition)

This file formalizes the paper's **Theorem 1 (Necessary and Sufficient Condition)**
as a Lean theorem. It establishes the equivalence between compositional
generalization (`CompositionalGeneralization`) and AS-UMR.

## Difference from the paper

The necessity direction in the paper relies on **Assumption 1** (test component
inputs must appear in training). In the formalization, we do not use axioms.
Instead, we make that assumption an explicit premise `h_seen` of the theorem,
just like `h_correct_train`. This makes the theorem statement clearer and
avoids introducing extra axioms.

## Theorem statement

Given model `M`, training set `train`, and test set `test`, under the two premises:
1. Training predictions are all correct: `correct_predictions M train`
2. All test component inputs have been seen in training:
   `seen_inputs_condition M train test`

Then the model provably enables compositional generalization
(`CompositionalGeneralization M train test`) iff it satisfies AS-UMR
(`AS_UMR M train test`).

Necessity is provided by `necessity_direction`; sufficiency by
`sufficiency_direction`.
-/

open TACG.Definitions
open TACG.Derivations.Necessity.NecessityDirection
open TACG.Derivations.Sufficiency.SufficiencyDirection

namespace TACG.Derivations.Theorems.NecessaryAndSufficientCondition

/-- Formal version of Theorem 1 (Necessary and Sufficient Condition).
    Premises `h_correct_train` and `h_seen` are explicit parameters, not axioms.
    Necessity: assume `CompositionalGeneralization` and prove AS-UMR.
    Sufficiency: directly invoke `sufficiency_direction`. -/
theorem necessary_and_sufficient_condition (M : Model) (train test : List Sample)
    (h_correct_train : correct_predictions M train)
    (h_seen : seen_inputs_condition M train test) :
    CompositionalGeneralization M train test ↔ AS_UMR M train test := by
  constructor
  · -- Necessity: assume compositional generalization holds, prove AS-UMR.
    intro h_cg
    exact necessity_direction M train test h_cg h_correct_train h_seen
  · -- Sufficiency: assume AS-UMR holds, prove compositional generalization.
    intro h_as_umr
    exact sufficiency_direction M train test h_as_umr

end TACG.Derivations.Theorems.NecessaryAndSufficientCondition
