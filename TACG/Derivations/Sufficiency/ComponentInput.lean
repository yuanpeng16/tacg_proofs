import TACG.Definitions
import TACG.Derivations.Sufficiency.InputNodePair
import TACG.Derivations.Helper.EEMap
import Mathlib.Data.List.Basic

open TACG.Definitions
open TACG.Derivations.Sufficiency.InputNodePair
open TACG.Derivations.Helper.EEMap

namespace TACG.Derivations.Sufficiency.ComponentInput

/-- The list of input values for a node in a graph. -/
def input_values (g : Graph) (n : Node) : List Value :=
  (g.node_inputs n).map g.node_value

/-- The list of input components for a node in a graph. -/
def input_components (g : Graph) (n : Node) : List Component :=
  (g.node_inputs n).map g.node_component

/-- Three-way match of inputs between hypothesis and reference graphs for
    two sample nodes: reference values match, reference components match,
    and hypothesis values match. -/
def inputs_match (M Z : Model) (A B : Sample) (zA zB : Node) : Prop :=
  input_values (Z.graphSet A) zA = input_values (Z.graphSet B) zB ∧
  input_components (Z.graphSet A) zA = input_components (Z.graphSet B) zB ∧
  input_values (M.graphSet A) zA = input_values (M.graphSet B) zB

/-- Helper: retrieving an element from a mapped list at a given index. -/
private lemma get_map {α β} (f : α → β) (l : List α) (i : ℕ) (h : i < l.length) :
    (l.map f).get ⟨i, by simp [List.length_map, h]⟩ = f (l.get ⟨i, h⟩) := by
  simp

/-- If reference input values and components match between A and B, and the
    induction hypothesis holds for each input node of zB, then the hypothesis
    input values also match. This is the core of the inductive step. -/
private lemma input_values_match
    {train test : List Sample} (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (h_inj : ∀ c ∈ components_list M train, InjectiveRepresentation c train M Z.model)
    (B : Sample) (hB : B ∈ test)
    (zB : Node) (zB_in : zB ∈ (Z.model.graphSet B).non_input_nodes)
    (A : Sample) (hA : A ∈ train)
    (zA : Node) (zA_in : zA ∈ (Z.model.graphSet A).non_input_nodes)
    (hvals : input_values (Z.model.graphSet A) zA = input_values (Z.model.graphSet B) zB)
    (hcomps : input_components (Z.model.graphSet A) zA = input_components (Z.model.graphSet B) zB)
    (h_inputs_eq_A : (M.graphSet A).node_inputs zA = (Z.model.graphSet A).node_inputs zA)
    (h_inputs_eq_B : (M.graphSet B).node_inputs zB = (Z.model.graphSet B).node_inputs zB)
    (h_ind : ∀ n ∈ (Z.model.graphSet B).node_inputs zB,
      ∃ (C : Sample) (zC : Node),
        C ∈ train ∧
        (zC ∈ (Z.model.graphSet C).input_nodes ∨
          zC ∈ (Z.model.graphSet C).non_input_nodes) ∧
        (M.graphSet C).node_component zC = (M.graphSet B).node_component n ∧
        (M.graphSet C).node_value zC = (M.graphSet B).node_value n ∧
        (Z.model.graphSet C).node_value zC = (Z.model.graphSet B).node_value n) :
    input_values (M.graphSet A) zA = input_values (M.graphSet B) zB := by
  unfold input_values
  rw [h_inputs_eq_A, h_inputs_eq_B]
  let insA := (Z.model.graphSet A).node_inputs zA
  let insB := (Z.model.graphSet B).node_inputs zB
  have len_eq_vals : insA.length = insB.length := by
    have hlen := congr_arg List.length hvals
    simp only [input_values, List.length_map] at hlen
    exact hlen
  have len_eq_map :
    (List.map (M.graphSet A).node_value insA).length =
    (List.map (M.graphSet B).node_value insB).length := by
    simp [List.length_map, len_eq_vals]
  apply List.ext_get
  · exact len_eq_map
  · intro i hi hi'
    have hiB : i < insB.length := by simpa [List.length_map] using hi'
    have hiA : i < insA.length := len_eq_vals.symm ▸ hiB
    let nB := insB[i]
    let nA := insA[i]
    let gA := Z.model.graphSet A
    let gB := Z.model.graphSet B
    have h_nA_in_inputs : nA ∈ gA.node_inputs zA := List.get_mem insA ⟨i, hiA⟩
    have h_nA_in_ordered : nA ∈ gA.input_nodes ++ gA.non_input_nodes :=
      by rw [Graph.non_input_nodes, ← List.append_assoc]; exact
      gA.input_nodes_in_graph zA nA h_nA_in_inputs
    have h_nB_in_inputs : nB ∈ gB.node_inputs zB := List.get_mem insB ⟨i, hiB⟩
    have h_nB_in_ordered : nB ∈ gB.input_nodes ++ gB.non_input_nodes :=
      by rw [Graph.non_input_nodes, ← List.append_assoc]; exact
      gB.input_nodes_in_graph zB nB h_nB_in_inputs
    have h_nA_in_Z : nA ∈ gA.input_nodes ∨ nA ∈ gA.non_input_nodes :=
      List.mem_append.mp h_nA_in_ordered
    have h_nB_in_Z : nB ∈ gB.input_nodes ∨ nB ∈ gB.non_input_nodes :=
      List.mem_append.mp h_nB_in_ordered
    -- Extract structural alignment equalities.
    have hA_in_all : A ∈ train ++ test := by rw [List.mem_append]; left; exact hA
    have hB_in_all : B ∈ train ++ test := by rw [List.mem_append]; right; exact hB
    obtain ⟨h_input_eq_A, h_inter_eq_A, h_out_eq_A, h_comp_eq_A⟩ := h_struct A hA_in_all
    obtain ⟨h_input_eq_B, h_inter_eq_B, h_out_eq_B, h_comp_eq_B⟩ := h_struct B hB_in_all
    have h_non_eq_B : (M.graphSet B).non_input_nodes = (Z.model.graphSet B).non_input_nodes := by
      rw [Graph.non_input_nodes, Graph.non_input_nodes]
      congr
    -- Prove nA and nB are not output nodes using output_not_used.
    have h_nA_not_out : nA ∉ gA.output_nodes := by
      intro h_out
      apply gA.output_not_used nA h_out zA
      · exact zA_in
      · exact h_nA_in_inputs
    have h_nB_not_out : nB ∉ gB.output_nodes := by
      intro h_out
      apply gB.output_not_used nB h_out zB
      · exact zB_in
      · exact h_nB_in_inputs
    -- Convert h_nA_in_Z and h_nB_in_Z to input ∨ intermediate.
    have h_nA_in_Z_inter : nA ∈ gA.input_nodes ∨ nA ∈ gA.intermediate_nodes := by
      rcases h_nA_in_Z with (h_in | h_non)
      · left; exact h_in
      · right
        rw [Graph.non_input_nodes] at h_non
        have h_non' := List.mem_append.mp h_non
        rcases h_non' with (h_inter | h_out)
        · exact h_inter
        · contradiction
    have h_nB_in_Z_inter : nB ∈ gB.input_nodes ∨ nB ∈ gB.intermediate_nodes := by
      rcases h_nB_in_Z with (h_in | h_non)
      · left; exact h_in
      · right
        rw [Graph.non_input_nodes] at h_non
        have h_non' := List.mem_append.mp h_non
        rcases h_non' with (h_inter | h_out)
        · exact h_inter
        · contradiction
    have hvals_eq :
      (Z.model.graphSet A).node_value nA = (Z.model.graphSet B).node_value nB :=
      get_eq_of_eq_map
        (Z.model.graphSet A).node_value
        (Z.model.graphSet B).node_value
        hvals i hiA hiB
    have hcomps_eq :
      (Z.model.graphSet A).node_component nA =
      (Z.model.graphSet B).node_component nB :=
      get_eq_of_eq_map
        (Z.model.graphSet A).node_component
        (Z.model.graphSet B).node_component
        hcomps i hiA hiB
    have h_ind_n := h_ind nB h_nB_in_inputs
    obtain ⟨C, zC, hC, h_node_in, hcomp_M, hval_M, hzval_Z⟩ := h_ind_n
    -- Prove zC is not an output node in the M graph.
    have hC_in_all : C ∈ train ++ test := by rw [List.mem_append]; left; exact hC
    obtain ⟨h_input_eq_C, h_inter_eq_C, h_out_eq_C, h_comp_eq_C⟩ := h_struct C hC_in_all
    have h_non_eq_C : (M.graphSet C).non_input_nodes = (Z.model.graphSet C).non_input_nodes := by
      rw [Graph.non_input_nodes, Graph.non_input_nodes]
      congr
    -- Input nodes and output nodes are disjoint (from ordered_nodup).
    have h_disjoint_in_out :
      List.Disjoint (M.graphSet C).input_nodes (M.graphSet C).output_nodes := by
      have h_nodup := (M.graphSet C).ordered_nodup
      rw [List.nodup_append] at h_nodup
      obtain ⟨_, _, h_dis⟩ := h_nodup
      intro x hx hy
      exact (h_dis x (List.mem_append_left (M.graphSet C).intermediate_nodes hx) x hy) rfl
    have h_zC_not_out_M : zC ∉ (M.graphSet C).output_nodes := by
      rcases h_node_in with (h_in | h_non)
      · -- zC is an input node; disjointness with outputs.
        have h_zC_in_M_input : zC ∈ (M.graphSet C).input_nodes :=
          by rw [h_input_eq_C]; exact h_in
        intro h_out
        exact h_disjoint_in_out h_zC_in_M_input h_out
      · -- zC is a non-input node.
        have h_zC_in_M_non : zC ∈ (M.graphSet C).non_input_nodes :=
          h_non_eq_C.symm ▸ h_non
        -- Prove nB is not an input node (else component would be inputComponent,
        -- contradicting that zC's non-input component equals it).
        have h_nB_not_input : nB ∉ (M.graphSet B).input_nodes := by
          intro h_in
          have h_comp_nB_input : (M.graphSet B).node_component nB = inputComponent :=
            (M.graphSet B).node_component_input nB h_in
          rw [h_comp_nB_input] at hcomp_M
          have h_zC_non_input_not_input : (M.graphSet C).node_component zC ≠ inputComponent :=
            (M.graphSet C).non_input_component_not_input zC h_zC_in_M_non
          exact h_zC_non_input_not_input hcomp_M
        -- From h_nB_in_Z_inter and h_nB_not_input, nB is intermediate.
        rcases h_nB_in_Z_inter with (h_nB_in | h_nB_inter)
        · -- nB is input, contradiction with h_nB_not_input.
          have h_nB_in_M := h_input_eq_B.symm ▸ h_nB_in
          contradiction
        · -- nB is intermediate, hence non-input.
          have h_nB_in_M_inter : nB ∈ (M.graphSet B).intermediate_nodes :=
            h_inter_eq_B.symm ▸ h_nB_inter
          have h_nB_in_M_non : nB ∈ (M.graphSet B).non_input_nodes :=
            by simp [Graph.non_input_nodes, h_nB_in_M_inter]
          -- nB is not output in Z ⇒ not output in M ⇒ component not output.
          have h_nB_not_out_M : nB ∉ (M.graphSet B).output_nodes :=
            by rw [h_out_eq_B]; exact h_nB_not_out
          have h_nB_comp_not_out : ¬((M.graphSet B).node_component nB).is_graph_output :=
            (M.graphSet B).output_component_consistency nB h_nB_in_M_non |>.not.mp h_nB_not_out_M
          -- zC component same as nB ⇒ not output ⇒ zC not output.
          have h_zC_comp_not_out : ¬((M.graphSet C).node_component zC).is_graph_output :=
            by rw [hcomp_M]; exact h_nB_comp_not_out
          intro h_out
          have h_out_comp : ((M.graphSet C).node_component zC).is_graph_output :=
            (M.graphSet C).output_component_consistency zC h_zC_in_M_non |>.mp h_out
          exact h_zC_comp_not_out h_out_comp
    -- By structural alignment, zC is not output in Z graph either.
    have h_zC_not_out_Z : zC ∉ (Z.model.graphSet C).output_nodes :=
      by rw [← h_out_eq_C]; exact h_zC_not_out_M
    -- Convert h_node_in to input ∨ intermediate for Z graph.
    have h_zC_in_Z_inter :
      zC ∈ (Z.model.graphSet C).input_nodes ∨ zC ∈ (Z.model.graphSet C).intermediate_nodes := by
      rcases h_node_in with (h_in | h_non)
      · left; exact h_in
      · right
        rw [Graph.non_input_nodes] at h_non
        have h_non' := List.mem_append.mp h_non
        rcases h_non' with (h_inter | h_out)
        · exact h_inter
        · contradiction
    -- Construct node_match and its witness, matching prove_input_node_pair.
    have h_node_match : node_match M Z.model train test h_struct C B zC nB :=
      ⟨hcomp_M, hval_M, hzval_Z⟩
    have h_ind_pair : ∃ (C0 : Sample) (zC0 : Node),
        C0 ∈ train ∧
        (zC0 ∈ (Z.model.graphSet C0).input_nodes ∨ zC0 ∈ (Z.model.graphSet C0).intermediate_nodes) ∧
        node_match M Z.model train test h_struct C0 B zC0 nB :=
      ⟨C, zC, hC, h_zC_in_Z_inter, h_node_match⟩
    -- Apply the proven input-node pair lemma.
    have hM_val_eq := prove_input_node_pair
      M Z.model train test h_struct h_inj B hB A hA nB nA
      h_nB_in_Z_inter h_nA_in_Z_inter hvals_eq hcomps_eq h_ind_pair
    have hiA_len : i < insA.length := hiA
    have hiB_len : i < insB.length := hiB
    rw [get_map (M.graphSet A).node_value insA i hiA_len,
        get_map (M.graphSet B).node_value insB i hiB_len]
    exact hM_val_eq

/-- Lemma 7: Component Input. Given structural alignment, injective representation
    for all used components, and the induction hypothesis for the inputs of a
    test node zB, there exists a training node zA whose inputs match those of zB
    in both reference and hypothesis. This is the key step for the induction. -/
lemma component_input
    {train test : List Sample} (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (h_inj : ∀ c ∈ components_list M train, InjectiveRepresentation c train M Z.model)
    (B : Sample) (hB : B ∈ test)
    (zB : Node) (zB_in : zB ∈ (Z.model.graphSet B).non_input_nodes)
    (h_ind : ∀ n ∈ (Z.model.graphSet B).node_inputs zB,
      ∃ (C : Sample) (zC : Node),
        C ∈ train ∧
        (zC ∈ (Z.model.graphSet C).input_nodes ∨
          zC ∈ (Z.model.graphSet C).non_input_nodes) ∧
        (M.graphSet C).node_component zC = (M.graphSet B).node_component n ∧
        (M.graphSet C).node_value zC = (M.graphSet B).node_value n ∧
        (Z.model.graphSet C).node_value zC = (Z.model.graphSet B).node_value n) :
    ∃ (A : Sample) (zA : Node),
      A ∈ train ∧
      zA ∈ (Z.model.graphSet A).non_input_nodes ∧
      (Z.model.graphSet A).node_component zA =
        (Z.model.graphSet B).node_component zB ∧
      inputs_match M Z.model A B zA zB := by
  -- By reference model property, there exists A,zA with matching reference inputs.
  obtain ⟨A, hA, zA, hzA, hcomp, hvals, hcomps⟩ :=
    Z.seen_inputs B hB zB zB_in
  have hA_in_all : A ∈ train ++ test := by
    rw [List.mem_append]; left; exact hA
  obtain ⟨h_input_eq_A, h_inter_eq_A, h_out_eq_A, h_comp_eq_A⟩ := h_struct A hA_in_all
  have h_non_eq_A : (M.graphSet A).non_input_nodes = (Z.model.graphSet A).non_input_nodes := by
    rw [Graph.non_input_nodes, Graph.non_input_nodes]
    congr
  have zA_in_M : zA ∈ (M.graphSet A).non_input_nodes :=
    h_non_eq_A.symm ▸ hzA
  have h_inputs_eq_A :
    (M.graphSet A).node_inputs zA = (Z.model.graphSet A).node_inputs zA :=
    (h_comp_eq_A zA zA_in_M).2
  have hB_in_all : B ∈ train ++ test := by
    rw [List.mem_append]; right; exact hB
  obtain ⟨h_input_eq_B, h_inter_eq_B, h_out_eq_B, h_comp_eq_B⟩ := h_struct B hB_in_all
  have h_non_eq_B : (M.graphSet B).non_input_nodes = (Z.model.graphSet B).non_input_nodes := by
    rw [Graph.non_input_nodes, Graph.non_input_nodes]
    congr
  have zB_in_M : zB ∈ (M.graphSet B).non_input_nodes :=
    h_non_eq_B.symm ▸ zB_in
  have h_inputs_eq_B :
    (M.graphSet B).node_inputs zB = (Z.model.graphSet B).node_inputs zB :=
    (h_comp_eq_B zB zB_in_M).2
  -- Use input_values_match to derive equality of hypothesis input values.
  have hM_eq := input_values_match Z M h_struct h_inj B hB zB zB_in A hA
    zA hzA hvals hcomps h_inputs_eq_A h_inputs_eq_B h_ind
  exact ⟨A, zA, hA, hzA, hcomp, ⟨hvals, hcomps, hM_eq⟩⟩

end TACG.Derivations.Sufficiency.ComponentInput
