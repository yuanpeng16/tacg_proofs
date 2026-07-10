# TACG: Formal Verification in Lean 4

**Formalization of:**  
*A Theoretical Analysis of Provable Compositional Generalization in Neural Networks: A Necessary and Sufficient Condition*

**Main project repository:** https://github.com/yuanpeng16/tacg

## Verification

    lake build
    # Build completed successfully (1942 jobs).

## Quick Start

For readers interested in the formalization:

- **[Definitions.lean](TACG/Definitions.lean)** – contains all core definitions (components, graphs, AS‑UMR, etc.).
- **[NecessaryAndSufficientCondition.lean](TACG/Derivations/Theorems/NecessaryAndSufficientCondition.lean)** – states the main theorem.

All proofs have been mechanically verified by Lean 4, so the derivation is fully formal and reliable.

## Main Files
- [TACG](TACG.lean)
- TACG
    - [Definitions](TACG/Definitions.lean)
    - Derivations
        - Mathematical Preliminaries
            - Lemma 5: [Cardinality Bound For In jectiveMappings](TACG/Derivations/MathematicalPreliminaries/CardinalityBoundForInjectiveMappings.lean)
            - Lemma 6: [Well-defined and Surjective Mappings](TACG/Derivations/MathematicalPreliminaries/WelldefinedAndSurjectiveMappings.lean)
            - Lemma 7: [Equal Set Size](TACG/Derivations/MathematicalPreliminaries/EqualSetSize.lean)
            - Lemma 1: [Mappings On Nodes](TACG/Derivations/MathematicalPreliminaries/MappingsOnNodes.lean)
        - Necessity
            - Lemma 8: [Reference Graph Set Construction](TACG/Derivations/Necessity/ReferenceGraphSetConstruction.lean)
            - Proposition 1: [Necessity](TACG/Derivations/Necessity/NecessityDirection.lean)
        - Sufficiency
            - Lemma 9: [Correct Training Prediction](TACG/Derivations/Sufficiency/CorrectTrainingPrediction.lean)
            - Lemma 10: [Deterministic Components](Derivations/Sufficiency/DeterministicComponents.lean)
            - Lemma 11: [Surjective Mapping](TACG/Derivations/Sufficiency/SurjectiveMapping.lean)
            - Lemma 12: [Injective Component Outputs](TACG/Derivations/Sufficiency/InjectiveComponentOutputs.lean)
            - Lemma 13: [Component Input](TACG/Derivations/Sufficiency/ComponentInput.lean)
            - Lemma 2: [Induction Step](TACG/Derivations/Sufficiency/InductionStep.lean)
            - Lemma 14: [Induction over the Graph](TACG/Derivations/Sufficiency/InductionOverGraph.lean)
            - Lemma 15: [Injective Mapping for Sufficiency](TACG/Derivations/Sufficiency/InjectiveMappingForSufficiency.lean)
            - Proposition 2: [Sufficiency](TACG/Derivations/Sufficiency/SufficiencyDirection.lean)
        - Theorem
            - Theorem 1: [Necessary and Sufficient Condition](TACG/Derivations/Theorems/NecessaryAndSufficientCondition.lean)
    - Example Approach
        - Lemma 16: [Entropy Decreases Under Event Merging](TACG/ExampleApproach/EntropyDecreasesUnderEventMerging.lean)
        - Lemma 3: [Minimum Entropy Implies Minimized Representation](TACG/ExampleApproach/MinimumEntropyImpliesMinimizedRepresentation.lean)
        - Corollary 1: [Example Approach Verification](TACG/ExampleApproach/ExampleApproachVerification.lean)
    - Minimal Example
        - Lemma 4: [Unambiguous Representation Verification](TACG/MinimalExample/UnambiguousRepresentationVerification.lean)
        - Corollary 2: [Minimal Example Verification](TACG/MinimalExample/MinimalExampleVerification.lean)
    - Discussion
        - Lemma 17: [Seen Test Inputs](TACG/Discussion/SeenTestInputs.lean)
        - Theorem 2: [Alternative Necessary and Sufficient Condition](TACG/Discussion/AlternativeNecessaryAndSufficientCondition.lean)
        - Corollary 3: [Injective Necessary and Sufficient Condition](TACG/Discussion/InjectiveNecessaryAndSufficientCondition.lean)

## Versions

Tested with Lean 4.30.0.
