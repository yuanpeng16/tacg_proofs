import TACG.Definitions
import TACG.Derivations.Helper.InputNodePairProcessing

open TACG.Definitions
open TACG.Derivations.Helper.InputNodePairProcessing

namespace TACG.Derivations.Sufficiency.InputNodePair

/-- Node match: the two nodes have equal components, equal hypothesis values,
    and equal reference values. Used in the induction step to relate nodes
    across samples. Note that ξ only applies to intermediate nodes. -/
def node_match (M Z : Model) (train test : List Sample)
    (_h_struct : StructuralAlignment M Z (train ++ test))
    (A B : Sample) (nA nB : Node) : Prop :=
  (M.graphSet A).node_component nA = (M.graphSet B).node_component nB ∧
  (M.graphSet A).node_value nA = (M.graphSet B).node_value nB ∧
  (Z.graphSet A).node_value nA = (Z.graphSet B).node_value nB

/-- If an intermediate node's value is in the reference graph for component c,
    then it belongs to ξ_set Z train c. This is used to construct membership
    proofs for injective representation. -/
private lemma node_value_in_ξ_set (Z : Model) (train : List Sample) (c : Component)
    (A : Sample) (hA : A ∈ train) (n : Node)
    (h_in : n ∈ (Z.graphSet A).intermediate_nodes)
    (h_comp : (Z.graphSet A).node_component n = c) :
    (Z.graphSet A).node_value n ∈ ξ_set Z train c := by
  unfold ξ_set
  rw [List.mem_toFinset]
  rw [List.mem_flatten]
  let L := (Z.graphSet A).intermediate_nodes
    |>.filter (fun out => decide ((Z.graphSet A).node_component out = c))
    |>.map (fun out => (Z.graphSet A).node_value out)
  use L
  constructor
  · rw [List.mem_map]
    use A, hA
  · rw [List.mem_map]
    use n
    constructor
    · rw [List.mem_filter]
      exact ⟨h_in, by simp [h_comp]⟩
    · rfl

/-- If two training intermediate nodes have the same reference value and same
    component, then by injective representation their hypothesis values are equal.
    This is a direct application of the injectivity of ξ_c on training data. -/
private lemma ref_eq_implies_hyp_eq
    (M Z : Model) (train test : List Sample)
    (h_struct : StructuralAlignment M Z (train ++ test))
    (h_inj : ∀ c ∈ components_list M train, InjectiveRepresentation c train M Z)
    (A C : Sample) (hA : A ∈ train) (hC : C ∈ train)
    (nA nC : Node)
    (h_nA_in : nA ∈ (Z.graphSet A).intermediate_nodes)
    (h_nC_in : nC ∈ (Z.graphSet C).intermediate_nodes)
    (h_val : (Z.graphSet A).node_value nA = (Z.graphSet C).node_value nC)
    (h_comp : (Z.graphSet A).node_component nA = (Z.graphSet C).node_component nC) :
    (M.graphSet A).node_value nA = (M.graphSet C).node_value nC := by
  have hA_in_all : A ∈ train ++ test := by rw [List.mem_append]; left; exact hA
  have hC_in_all : C ∈ train ++ test := by rw [List.mem_append]; left; exact hC
  obtain ⟨h_input_eq_A, h_inter_eq_A, h_out_eq_A, h_comp_eq_A⟩ := h_struct A hA_in_all
  obtain ⟨h_input_eq_C, h_inter_eq_C, h_out_eq_C, h_comp_eq_C⟩ := h_struct C hC_in_all
  -- Structural alignment gives equal intermediate node lists.
  have nA_in_M : nA ∈ (M.graphSet A).intermediate_nodes := h_inter_eq_A.symm ▸ h_nA_in
  have nC_in_M : nC ∈ (M.graphSet C).intermediate_nodes := h_inter_eq_C.symm ▸ h_nC_in
  -- Intermediate nodes are also non-input nodes for component equality.
  have nA_in_M_non : nA ∈ (M.graphSet A).non_input_nodes :=
    by simp [Graph.non_input_nodes, nA_in_M]
  have nC_in_M_non : nC ∈ (M.graphSet C).non_input_nodes :=
    by simp [Graph.non_input_nodes, nC_in_M]
  -- Components are the same in M and Z by structural alignment.
  have compA_M : (M.graphSet A).node_component nA = (Z.graphSet A).node_component nA :=
    (h_comp_eq_A nA nA_in_M_non).1
  have compC_M : (M.graphSet C).node_component nC = (Z.graphSet C).node_component nC :=
    (h_comp_eq_C nC nC_in_M_non).1
  let c := (Z.graphSet A).node_component nA
  let hA_val := (M.graphSet A).node_value nA
  let zA_val := (Z.graphSet A).node_value nA
  let hC_val := (M.graphSet C).node_value nC
  let zC_val := (Z.graphSet C).node_value nC
  -- Construct ξ relations for both nodes.
  have ξ_left : ξ M Z train c hA_val zA_val :=
    ⟨A, hA, nA, nA_in_M, by rw [compA_M], rfl, rfl⟩
  have ξ_right : ξ M Z train c hC_val zC_val :=
    ⟨C, hC, nC, nC_in_M, by rw [compC_M, ← h_comp], rfl, rfl⟩
  -- zC_val is in ξ_set Z, so we can apply injectivity.
  have z_in := node_value_in_ξ_set Z train c C hC nC h_nC_in h_comp.symm
  have z_eq : zA_val = zC_val := h_val
  have ξ_left' : ξ M Z train c hA_val zC_val := by rw [z_eq] at ξ_left; exact ξ_left
  -- Component c is in the used components list.
  have hc : c ∈ components_list M train := by
    unfold components_list
    rw [List.mem_dedup]
    apply List.mem_flatten.mpr
    use (M.graphSet A).intermediate_nodes.map (M.graphSet A).node_component
    constructor
    · rw [List.mem_map]
      use A, hA
    · rw [List.mem_map]
      use nA
  let h_inj_c := h_inj c hc
  exact h_inj_c ((Z.graphSet C).node_value nC) z_in hA_val hC_val ξ_left' ξ_right

/-- Non-input case for input-node pair lemma. When both nA and nB are intermediate
    nodes, use the induction witness C,zC to connect nB to training and then
    apply ref_eq_implies_hyp_eq. -/
private lemma input_node_pair_noninput_case
    (M Z : Model) (train test : List Sample)
    (h_struct : StructuralAlignment M Z (train ++ test))
    (h_inj : ∀ c ∈ components_list M train, InjectiveRepresentation c train M Z)
    (B : Sample) (hB : B ∈ test)
    (A : Sample) (hA : A ∈ train)
    (nB nA : Node)
    (h_nB_in_Z : nB ∈ (Z.graphSet B).intermediate_nodes)
    (h_nA_in_Z : nA ∈ (Z.graphSet A).intermediate_nodes)
    (hvals_eq : (Z.graphSet A).node_value nA = (Z.graphSet B).node_value nB)
    (hcomps_eq : (Z.graphSet A).node_component nA = (Z.graphSet B).node_component nB)
    (h_ind : ∃ (C : Sample) (zC : Node),
        C ∈ train ∧
        (zC ∈ (Z.graphSet C).input_nodes ∨ zC ∈ (Z.graphSet C).intermediate_nodes) ∧
        node_match M Z train test h_struct C B zC nB) :
    (M.graphSet A).node_value nA = (M.graphSet B).node_value nB := by
  obtain ⟨C, zC, hC, h_node_in, h_match⟩ := h_ind
  have hcompC := h_match.1
  have hhypC := h_match.2.1
  have hvalC := h_match.2.2
  have hB_in_all : B ∈ train ++ test := by rw [List.mem_append]; right; exact hB
  obtain ⟨h_input_eq_B, h_inter_eq_B, h_out_eq_B, h_comp_eq_B⟩ := h_struct B hB_in_all
  -- Structural alignment: intermediate node lists are equal.
  have h_nB_in_M_inter : nB ∈ (M.graphSet B).intermediate_nodes :=
    h_inter_eq_B.symm ▸ h_nB_in_Z
  have h_nB_in_M_non : nB ∈ (M.graphSet B).non_input_nodes :=
    by simp [Graph.non_input_nodes, h_nB_in_M_inter]
  have h_nB_comp_ne : (M.graphSet B).node_component nB ≠ inputComponent :=
    (M.graphSet B).non_input_component_not_input nB h_nB_in_M_non
  have hC_in_all : C ∈ train ++ test := by rw [List.mem_append]; left; exact hC
  obtain ⟨h_input_eq_C, h_inter_eq_C, h_out_eq_C, h_comp_eq_C⟩ := h_struct C hC_in_all
  -- Determine whether zC is an intermediate node.
  have h_zC_in_M_inter : zC ∈ (M.graphSet C).intermediate_nodes := by
    rcases h_node_in with (h_in_input | h_in_inter)
    · have h_zC_in_M_input : zC ∈ (M.graphSet C).input_nodes :=
        h_input_eq_C.symm ▸ h_in_input
      have h_comp_M_input : (M.graphSet C).node_component zC = inputComponent :=
        (M.graphSet C).node_component_input zC h_zC_in_M_input
      rw [h_comp_M_input] at hcompC
      rw [hcompC] at h_nB_comp_ne
      contradiction
    · exact h_inter_eq_C.symm ▸ h_in_inter
  have h_zC_in_M_non : zC ∈ (M.graphSet C).non_input_nodes :=
    by simp [Graph.non_input_nodes, h_zC_in_M_inter]
  have h_zC_in_inter : zC ∈ (Z.graphSet C).intermediate_nodes :=
    h_inter_eq_C ▸ h_zC_in_M_inter
  -- Reference component of zC equals that of nB.
  have h_comp_zC_ref_eq :
      (Z.graphSet C).node_component zC = (Z.graphSet B).node_component nB := by
    have h1 := (h_comp_eq_C zC h_zC_in_M_non).1
    have h2 := hcompC
    have h3 := (h_comp_eq_B nB h_nB_in_M_non).1
    exact h1.symm.trans (h2.trans h3)
  -- Transitivity of reference values and components.
  have h_val_trans : (Z.graphSet A).node_value nA = (Z.graphSet C).node_value zC :=
    hvals_eq.trans hvalC.symm
  have h_comp_trans :
      (Z.graphSet A).node_component nA = (Z.graphSet C).node_component zC :=
    hcomps_eq.trans h_comp_zC_ref_eq.symm
  -- Apply ref_eq_implies_hyp_eq to get equality of hypothesis values.
  have hM_eq := ref_eq_implies_hyp_eq M Z train test h_struct h_inj A C hA hC nA zC
    h_nA_in_Z h_zC_in_inter h_val_trans h_comp_trans
  exact hM_eq.trans hhypC

/-- Main lemma: for input nodes (either input or intermediate) that match in
    reference values and components, their hypothesis values are equal.
    This handles the two cases: input nodes (use input_node_pair_input_case)
    and intermediate nodes (use input_node_pair_noninput_case). -/
lemma prove_input_node_pair
    (M Z : Model) (train test : List Sample)
    (h_struct : StructuralAlignment M Z (train ++ test))
    (h_inj : ∀ c ∈ components_list M train, InjectiveRepresentation c train M Z)
    (B : Sample) (hB : B ∈ test)
    (A : Sample) (hA : A ∈ train)
    (nB nA : Node)
    (h_nB_in_Z : nB ∈ (Z.graphSet B).input_nodes ∨ nB ∈ (Z.graphSet B).intermediate_nodes)
    (h_nA_in_Z : nA ∈ (Z.graphSet A).input_nodes ∨ nA ∈ (Z.graphSet A).intermediate_nodes)
    (hvals_eq : (Z.graphSet A).node_value nA = (Z.graphSet B).node_value nB)
    (hcomps_eq : (Z.graphSet A).node_component nA = (Z.graphSet B).node_component nB)
    (h_ind : ∃ (C : Sample) (zC : Node),
        C ∈ train ∧
        (zC ∈ (Z.graphSet C).input_nodes ∨ zC ∈ (Z.graphSet C).intermediate_nodes) ∧
        node_match M Z train test h_struct C B zC nB) :
    (M.graphSet A).node_value nA = (M.graphSet B).node_value nB := by
  match h_nB_in_Z with
  | Or.inl h_nB_in_input =>
      -- nB is input: nA must also be input (otherwise component types conflict).
      have h_nA_in_input : nA ∈ (Z.graphSet A).input_nodes := by
        match h_nA_in_Z with
        | Or.inl h => exact h
        | Or.inr h_inter =>
          have h_nB_comp : (Z.graphSet B).node_component nB = inputComponent :=
            (Z.graphSet B).node_component_input nB h_nB_in_input
          have h_nA_comp : (Z.graphSet A).node_component nA = inputComponent :=
            hcomps_eq.symm ▸ h_nB_comp
          have : (Z.graphSet A).node_component nA ≠ inputComponent :=
            (Z.graphSet A).non_input_component_not_input nA
              (by simp [h_inter])
          contradiction
      exact input_node_pair_input_case M Z train test h_struct B hB A hA nB nA
        h_nB_in_input h_nA_in_input hvals_eq
  | Or.inr h_nB_in_inter =>
      -- nB is intermediate: nA must also be intermediate.
      have h_nA_in_inter : nA ∈ (Z.graphSet A).intermediate_nodes := by
        match h_nA_in_Z with
        | Or.inr h => exact h
        | Or.inl h_input =>
          have h_nA_comp : (Z.graphSet A).node_component nA = inputComponent :=
            (Z.graphSet A).node_component_input nA h_input
          have h_nB_comp := hcomps_eq ▸ h_nA_comp
          have : (Z.graphSet B).node_component nB ≠ inputComponent :=
            (Z.graphSet B).non_input_component_not_input nB
              (by simp [h_nB_in_inter])
          contradiction
      exact input_node_pair_noninput_case M Z train test h_struct h_inj B hB A hA nB nA
        h_nB_in_inter h_nA_in_inter hvals_eq hcomps_eq h_ind

end TACG.Derivations.Sufficiency.InputNodePair
