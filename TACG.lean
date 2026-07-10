import TACG.Derivations.Theorems.NecessaryAndSufficientCondition
import TACG.ExampleApproach.ExampleApproachVerification
import TACG.MinimalExample.MinimalExampleVerification
import TACG.Discussion.AlternativeNecessaryAndSufficientCondition
import TACG.Discussion.InjectiveNecessaryAndSufficientCondition

/-!
# TACG: Formal Verification in Lean 4

This file aggregates the main formalized results of the paper.
All theorems and corollaries are mechanically verified in Lean 4.

## Formalized Results

- **`TACG.Derivations.Theorems.NecessaryAndSufficientCondition`**:
  Theorem 1 (Necessary and Sufficient Condition) — the core equivalence
  between compositional generalization and AS-UMR.

- **`TACG.ExampleApproach.ExampleApproachVerification`**:
  Corollary 1 (Example Approach Verification) — correctness of the
  proposed algorithm when minimum entropy is achieved.

- **`TACG.MinimalExample.MinimalExampleVerification`**:
  Corollary 2 (Minimal Example Verification) — correctness on the
  three-input XOR task under the minimized representation condition.

- **`TACG.Discussion.AlternativeNecessaryAndSufficientCondition`**:
  Theorem 2 (Alternative Necessary and Sufficient Condition) — the
  equivalence where "seen test inputs" is part of the definition.

- **`TACG.Discussion.InjectiveNecessaryAndSufficientCondition`**:
  Corollary 3 (Injective Necessary and Sufficient Condition) — the
  equivalent condition using injective representation (AS-IR).
-/
