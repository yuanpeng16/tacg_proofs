# TACG: Formal Verification in Lean 4

*A Theoretical Analysis of Provable Compositional Generalization in Neural Networks: A Necessary and Sufficient Condition*

**Main project repository:** https://github.com/yuanpeng16/tacg

The proofs are machine-checked by Lean 4. The key files are:
- **[Definitions.lean](TACG/Definitions.lean)** – core definitions
- **[NecessaryAndSufficientCondition.lean](TACG/Derivations/Theorems/NecessaryAndSufficientCondition.lean)** – main theorem

## Verification

```bash
lake build
```

Output:

```
Build completed successfully (1941 jobs).
```

## Main Files

Listed below are the files corresponding to lemmas, propositions, and theorems from the paper.  
Files not listed are auxiliary.
- [TACG](TACG.lean)
- TACG
    - [Definitions](TACG/Definitions.lean)
    - Derivations
        - Mathematical Preliminaries
            - Lemma 1: [Mappings On Nodes](TACG/Derivations/MathematicalPreliminaries/MappingsOnNodes.lean)
        - Necessity
            - Proposition 1: [Necessity](TACG/Derivations/Necessity/NecessityDirection.lean)
        - Sufficiency
            - Lemma 5: [Surjective Mapping](TACG/Derivations/Sufficiency/SurjectiveMapping.lean)
            - Lemma 6: [Injective Component Outputs](TACG/Derivations/Sufficiency/InjectiveComponentOutputs.lean)
            - Lemma 7: [Component Input](TACG/Derivations/Sufficiency/ComponentInput.lean)
            - Lemma 2: [Inductive Step](TACG/Derivations/Sufficiency/InductiveStep.lean)
            - Lemma 8: [Induction over the Graph](TACG/Derivations/Sufficiency/InductionOverGraph.lean)
            - Lemma 9: [Injective Mapping for Sufficiency](TACG/Derivations/Sufficiency/InjectiveMappingForSufficiency.lean)
            - Proposition 2: [Sufficiency](TACG/Derivations/Sufficiency/SufficiencyDirection.lean)
        - Theorem
            - Theorem 1: [Necessary and Sufficient Condition](TACG/Derivations/Theorems/NecessaryAndSufficientCondition.lean)
    - Example Approach
        - Lemma 10: [Entropy Decreases Under Event Merging](TACG/ExampleApproach/EntropyDecreasesUnderEventMerging.lean)
        - Lemma 3: [Minimum Entropy Implies Minimized Representation](TACG/ExampleApproach/MinimumEntropyImpliesMinimizedRepresentation.lean)
        - Corollary 1: [Example Approach Verification](TACG/ExampleApproach/ExampleApproachVerification.lean)
    - Minimal Example
        - Lemma 4: [Unambiguous Representation Verification](TACG/MinimalExample/UnambiguousRepresentationVerification.lean)
        - Corollary 2: [Minimal Example Verification](TACG/MinimalExample/MinimalExampleVerification.lean)
    - Discussion
        - Lemma 11: [Seen Test Component Inputs](TACG/Discussion/SeenTestComponentInputs.lean)
        - Theorem 2: [Alternative Necessary and Sufficient Condition](TACG/Discussion/AlternativeNecessaryAndSufficientCondition.lean)
        - Corollary 3: [Necessary and Sufficient Condition via Injectivity](TACG/Discussion/NecessaryAndSufficientConditionViaInjectivity.lean)

## Versions

Tested with Lean 4.30.0.
