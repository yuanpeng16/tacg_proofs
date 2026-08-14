import TACG.Definitions
import TACG.Derivations.Sufficiency.InductionOverGraph
import TACG.Derivations.Helper.EEMap

open TACG.Definitions
open TACG.Derivations.Sufficiency.InductionOverGraph
open TACG.Derivations.Helper.EEMap

namespace TACG.Derivations.Sufficiency.InjectiveMappingForSufficiency

/-- Helper: if a model is correct on a dataset, then the value of an output node
    in its graph equals the sample's expected output for that node. -/
private lemma output_node_value_eq {model : Model} {dataset : List Sample} {s : Sample} {n : Node}
    (h_correct : correct_predictions model dataset)
    (hs : s ∈ dataset)
    (hn : n ∈ (model.graphSet s).output_nodes) :
    (model.graphSet s).node_value n = s.output n := by
  unfold correct_predictions at h_correct
  specialize h_correct s hs
  let g := model.graphSet s
  have h_mem := List.mem_iff_get.mp hn
  obtain ⟨⟨i, h_lt⟩, hi⟩ := h_mem
  have h_eq := get_eq_of_eq_map g.node_value s.output h_correct i h_lt h_lt
  rw [hi] at h_eq
  simpa [g] using h_eq

/-- Lemma 14 (Injective Mapping for Sufficiency).
    If a model has structural alignment with a reference model and has injective
    representation for all used components, then it provably enables compositional
    generalization. The proof uses induction over the graph to match every test
    output node with a training output node, then applies correctness of training
    and reference predictions. -/
lemma injective_mapping_for_sufficiency
    {train test : List Sample} {M : Model}
    (Z : ReferenceModel train test)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (h_inj : ∀ c ∈ components_list M train, InjectiveRepresentation c train M Z.model) :
    CompositionalGeneralization M train test := by
  unfold CompositionalGeneralization
  intro h_train_correct B hB
  obtain ⟨_, h_non_eq, h_out_eq, _⟩ := h_struct B (by simp [hB])
  dsimp only
  -- The output nodes of M and Z are identical by structural alignment.
  rw [h_out_eq]
  -- We need to show that for every output node, the model's value equals the sample's output.
  rw [List.map_eq_map_iff]
  intro outB h_outB
  have h_outB_noninput_Z : outB ∈ (Z.model.graphSet B).non_input_nodes := by
    rw [Graph.non_input_nodes]
    exact List.mem_append_right (Z.model.graphSet B).intermediate_nodes h_outB
  have h_mem_union : outB ∈ (Z.model.graphSet B).input_nodes ∪
                     (Z.model.graphSet B).non_input_nodes :=
    List.mem_union_right (Z.model.graphSet B).input_nodes h_outB_noninput_Z
  -- By induction over the graph, there exists a training node zA matching outB.
  have ind_result := induction_over_graph Z M h_struct h_inj B hB outB h_mem_union
  rcases ind_result with ⟨A, zA, hA, hzA_mem, hcomp, hvalZ, hvalM⟩
  let c := (Z.model.graphSet B).node_component outB
  -- Since outB is an output node, its component must be marked as graph output.
  have h_c_out : c.is_graph_output = true := by
    exact ((Z.model.graphSet B).output_component_consistency outB
           h_outB_noninput_Z).mp h_outB
  have h_zA_in_Z : (Z.model.graphSet A).node_component zA = c := hcomp
  -- Show zA is a non-input node in Z, hence by output consistency it is an output node.
  have h_zA_noninput_Z : zA ∈ (Z.model.graphSet A).non_input_nodes := by
    have h_ne_input : (Z.model.graphSet A).node_component zA ≠ inputComponent := by
      rw [h_zA_in_Z]
      intro heq
      rw [heq] at h_c_out
      simp only [inputComponent] at h_c_out
      contradiction
    rcases List.mem_append.mp hzA_mem with (h_in | h_non)
    · exfalso; apply h_ne_input; exact (Z.model.graphSet A).node_component_input zA h_in
    · exact h_non
  have h_zA_output_in_Z : zA ∈ (Z.model.graphSet A).output_nodes := by
    exact ((Z.model.graphSet A).output_component_consistency zA h_zA_noninput_Z).mpr
      (by rw [h_zA_in_Z]; exact h_c_out)
  -- Structural alignment ensures zA is also an output node in M.
  have h_zA_output_in_M : zA ∈ (M.graphSet A).output_nodes := by
    obtain ⟨_, _, h_out_eq_A, _⟩ := h_struct A (by simp [hA])
    rw [← h_out_eq_A] at h_zA_output_in_Z
    exact h_zA_output_in_Z
  -- Training correctness gives M's value equals A's output.
  have h_train_out : (M.graphSet A).node_value zA = A.output zA :=
    output_node_value_eq h_train_correct hA h_zA_output_in_M
  have hA_in_all : A ∈ train ++ test := by simp [hA]
  -- Reference correctness gives A's output equals Z's reference value.
  have h_ref_out : A.output zA = (Z.model.graphSet A).node_value zA :=
    (output_node_value_eq Z.correctness hA_in_all h_zA_output_in_Z).symm
  have hB_in_all : B ∈ train ++ test := by simp [hB]
  -- Reference correctness for the test output node.
  have hZ_correct_outB : (Z.model.graphSet B).node_value outB = B.output outB :=
    output_node_value_eq Z.correctness hB_in_all h_outB
  -- Chain equalities: M value = training output = reference value = test output.
  rw [← hvalM, h_train_out, h_ref_out, hvalZ, hZ_correct_outB]

end TACG.Derivations.Sufficiency.InjectiveMappingForSufficiency
