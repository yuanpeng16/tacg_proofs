import TACG.Definitions
import TACG.Derivations.Necessity.ReferenceGraphSetConstruction

open TACG.Definitions
open TACG.Derivations.Necessity.ReferenceGraphSetConstruction

namespace TACG.Derivations.Necessity.NecessityDirection

/-- Proposition 1 (Necessity): if a model provably enables compositional generalization,
    then it satisfies AS-UMR. This lemma constructs the reference model from the
    hypothesis model itself and verifies the three conditions. -/
lemma necessity_direction (M : Model) (train test : List Sample)
    (h_cg : CompositionalGeneralization M train test)
    (h_correct_train : correct_predictions M train)
    (h_seen : seen_inputs_condition M train test) :
    AS_UMR M train test := by
  -- Build a reference model Z from M using the reference graph set construction.
  obtain ⟨Z, hZ_eq, h_struc, _⟩ :=
    reference_graph_set_construction M train test h_correct_train h_cg h_seen
  -- Structural alignment holds because Z is identical to M on graph structure.
  have h_struc' : StructuralAlignment M Z.model (train ++ test) := by
    rw [hZ_eq]; exact h_struc
  -- For every used component, both unambiguous and minimized representations hold.
  have unamb_min : ∀ c ∈ components_list M train,
      UnambiguousRepresentation c train M Z.model ∧
      MinimizedRepresentation c train M Z.model := by
    intro c hc
    -- Unambiguous: Z = M, so each hypothesis value maps to exactly itself.
    have unamb : UnambiguousRepresentation c train M Z.model := by
      rw [hZ_eq]
      unfold UnambiguousRepresentation
      intros h_val _ z1 z2 rel1 rel2
      have eq1 := self_ξ_eq M train c h_val z1 rel1
      have eq2 := self_ξ_eq M train c h_val z2 rel2
      exact eq1.symm.trans eq2
    -- Minimized: the ξ_set for M and Z are identical, so cardinalities are equal.
    have minimized : MinimizedRepresentation c train M Z.model := by
      rw [hZ_eq]
      unfold MinimizedRepresentation
      rfl
    exact ⟨unamb, minimized⟩
  -- Conclude AS-UMR with the constructed reference model.
  exact ⟨Z, h_struc', unamb_min⟩

end TACG.Derivations.Necessity.NecessityDirection
