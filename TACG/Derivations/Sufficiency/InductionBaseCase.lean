import TACG.Definitions
import TACG.Derivations.Helper.InputNodePairProcessing
import TACG.Derivations.Helper.EEMap

open TACG.Definitions
open TACG.Derivations.Helper.InputNodePairProcessing
open TACG.Derivations.Helper.EEMap

namespace TACG.Derivations.Sufficiency.InductionBaseCase

/-- Base case for induction over the graph: for any input node of a test sample,
    there exists a node in some training sample that matches it in both
    reference value and hypothesis value, and has the same component.
    This uses the no-dangling-node property and the reference model's seen
    inputs condition to find a non-input node whose inputs contain n,
    then extracts n from the matched inputs. -/
lemma input_node_match_from_noninput
    {train test : List Sample} (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (B : Sample) (hB : B ∈ test)
    (n : Node) (h_n_in : n ∈ (Z.model.graphSet B).input_nodes) :
    ∃ (A : Sample) (zA : Node),
      A ∈ train ∧
      zA ∈ (Z.model.graphSet A).input_nodes ++ (Z.model.graphSet A).non_input_nodes ∧
      (Z.model.graphSet A).node_component zA = (Z.model.graphSet B).node_component n ∧
      (Z.model.graphSet A).node_value zA = (Z.model.graphSet B).node_value n ∧
      (M.graphSet A).node_value zA = (M.graphSet B).node_value n := by
  let gB := Z.model.graphSet B
  -- n is an input node, hence it appears in input_nodes ++ intermediate_nodes.
  have h_n_in_nonoutput : n ∈ gB.input_nodes ++ gB.intermediate_nodes :=
    List.mem_append_left (gB.intermediate_nodes) h_n_in
  -- By no_dangling_nodes, n is used as input to some non-input node m.
  rcases gB.no_dangling_nodes n h_n_in_nonoutput with ⟨m, hm_noninput, hn_in_inputs⟩
  -- By seen_inputs_condition, there is a training node zA whose inputs match m.
  rcases Z.seen_inputs B hB m hm_noninput with ⟨A, hA, zA, hzA, hcomp, hvals, hcomps⟩
  let insB := gB.node_inputs m
  -- Find the index i where n appears in the input list of m.
  rcases List.mem_iff_get.mp hn_in_inputs with ⟨i, hi_eq⟩
  let i_val : ℕ := i.val
  have hiB : i_val < insB.length := i.2
  let insA := (Z.model.graphSet A).node_inputs zA
  -- Input lists have equal length from hvals.
  have hlen : insA.length = insB.length := by
    have := congr_arg List.length hvals
    simpa [List.length_map] using this
  have hiA : i_val < insA.length := by
    rw [hlen]
    exact hiB
  -- Extract the i-th input node of zA.
  let zA_i := insA.get ⟨i_val, hiA⟩
  -- Its reference value equals n's reference value.
  have hval_eq : (Z.model.graphSet A).node_value zA_i = gB.node_value n := by
    have h := get_eq_of_eq_map (Z.model.graphSet A).node_value gB.node_value hvals i_val hiA hiB
    rw [hi_eq] at h
    exact h
  -- Its component equals n's component.
  have hcomp_eq : (Z.model.graphSet A).node_component zA_i = gB.node_component n := by
    have h :=
      get_eq_of_eq_map (Z.model.graphSet A).node_component gB.node_component hcomps i_val hiA hiB
    rw [hi_eq] at h
    exact h
  -- Since n is an input node, its component is inputComponent, so zA_i is also an input node.
  have h_zA_i_is_input : zA_i ∈ (Z.model.graphSet A).input_nodes := by
    have h_comp : (Z.model.graphSet A).node_component zA_i = inputComponent := by
      rw [hcomp_eq, (Z.model.graphSet B).node_component_input n h_n_in]
    have h_mem_union : zA_i ∈ (Z.model.graphSet A).input_nodes ++
        (Z.model.graphSet A).non_input_nodes := by
      rw [Graph.non_input_nodes, ← List.append_assoc]
      exact (Z.model.graphSet A).input_nodes_in_graph zA zA_i (List.get_mem insA ⟨i_val, hiA⟩)
    rcases List.mem_append.mp h_mem_union with (h | h_non)
    · exact h
    · exact absurd h_comp ((Z.model.graphSet A).non_input_component_not_input zA_i h_non)
  -- Use the input-node pair lemma to get equality of hypothesis values.
  have h_hyp_eq :=
    input_node_pair_input_case M Z.model train test h_struct B hB A hA n zA_i
      h_n_in h_zA_i_is_input hval_eq
  -- Package the result.
  exact ⟨A, zA_i, hA, List.mem_append.mpr (Or.inl h_zA_i_is_input), hcomp_eq, hval_eq, h_hyp_eq⟩

end TACG.Derivations.Sufficiency.InductionBaseCase
