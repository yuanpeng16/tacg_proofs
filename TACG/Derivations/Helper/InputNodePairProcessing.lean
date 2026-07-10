import TACG.Definitions

open TACG.Definitions

namespace TACG.Derivations.Helper.InputNodePairProcessing

/-- If two input nodes have equal reference values across a train and a test sample,
    then their model input values are also equal, using structural alignment and
    the input_nodes_correct property. -/
lemma input_node_pair_input_case
    (M Z : Model) (train test : List Sample)
    (h_struct : StructuralAlignment M Z (train ++ test))
    (B : Sample) (hB : B ∈ test)
    (A : Sample) (hA : A ∈ train)
    (nB nA : Node)
    (h_nB_in_Z : nB ∈ (Z.graphSet B).input_nodes)
    (h_nA_in_Z : nA ∈ (Z.graphSet A).input_nodes)
    (hvals_eq : (Z.graphSet A).node_value nA = (Z.graphSet B).node_value nB) :
    (M.graphSet A).node_value nA = (M.graphSet B).node_value nB := by
  have hA_in_all : A ∈ train ++ test := List.mem_append_left _ hA
  have hB_in_all : B ∈ train ++ test := List.mem_append_right _ hB
  have ⟨h_input_eq_A, _, _, _⟩ := h_struct A hA_in_all
  have ⟨h_input_eq_B, _, _, _⟩ := h_struct B hB_in_all
  rw [M.input_nodes_correct A nA (h_input_eq_A.symm ▸ h_nA_in_Z),
      M.input_nodes_correct B nB (h_input_eq_B.symm ▸ h_nB_in_Z)]
  rw [← Z.input_nodes_correct A nA h_nA_in_Z, ← Z.input_nodes_correct B nB h_nB_in_Z]
  exact hvals_eq

end TACG.Derivations.Helper.InputNodePairProcessing
