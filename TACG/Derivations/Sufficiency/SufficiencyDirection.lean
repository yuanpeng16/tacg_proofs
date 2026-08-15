import TACG.Definitions
import TACG.Derivations.Sufficiency.InjectiveComponentOutputs
import TACG.Derivations.Sufficiency.InjectiveMappingForSufficiency

open TACG.Definitions
open TACG.Derivations.Sufficiency.InjectiveComponentOutputs
open TACG.Derivations.Sufficiency.InjectiveMappingForSufficiency

namespace TACG.Derivations.Sufficiency.SufficiencyDirection

/-- Proposition 2 (Sufficiency) from the paper.
    If a model has AS-UMR (Aligned Structure-Unambiguous Minimized Representation),
    then it provably enables compositional generalization.
    The proof: from AS-UMR we derive injective representation for all used
    components (Lemma 6), then apply the injective mapping sufficiency lemma
    (Lemma 9) to obtain compositional generalization. -/
lemma sufficiency_direction (M : Model) (train test : List Sample)
    (h_as_umr : AS_UMR M train test) :
    CompositionalGeneralization M train test := by
  -- Extract the reference model and the three AS-UMR conditions.
  rcases h_as_umr with ⟨Z, h_struct, h_cond⟩
  -- For every used component, unambiguous + minimized => injective representation.
  have h_inj : ∀ c ∈ components_list M train, InjectiveRepresentation c train M Z.model := by
    intros c hc
    rcases h_cond c hc with ⟨h_unamb, h_min⟩
    have h_struct_train : StructuralAlignment M Z.model train := by
      unfold StructuralAlignment
      intro s hs
      exact h_struct s (by simp [hs])
    exact injective_component_outputs M Z.model train c h_struct_train h_unamb h_min
  -- With structural alignment and injective representation, apply the sufficiency lemma.
  exact injective_mapping_for_sufficiency Z h_struct h_inj

end TACG.Derivations.Sufficiency.SufficiencyDirection
