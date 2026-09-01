import TACG.Definitions
import TACG.Derivations.Sufficiency.InductiveStep
import TACG.Derivations.Sufficiency.InductionBaseCase
import TACG.Derivations.Sufficiency.IndexTopology

open TACG.Definitions
open TACG.Derivations.Sufficiency.InductiveStep
open TACG.Derivations.Sufficiency.InductionBaseCase
open TACG.Derivations.Sufficiency.IndexTopology

namespace TACG.Derivations.Sufficiency.InductionOverGraph

/-- Lemma 8: Induction over the Graph.
    If structural alignment and injective representation hold for all used
    components, then for every node in a test graph (input or non-input),
    there exists a training graph node with the same component, same reference
    value, and same hypothesis value. This is proved by well-founded induction
    on the topological order using the inductive step lemma and the base case. -/
lemma induction_over_graph
    {train test : List Sample} (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (h_inj : ∀ c ∈ components_list M train,
      InjectiveRepresentation c train M Z.model)
    (B : Sample) (hB : B ∈ test) :
    ∀ (zB : Node), zB ∈ (Z.model.graphSet B).input_nodes ∪
        (Z.model.graphSet B).non_input_nodes →
      ∃ (A : Sample) (zA : Node),
        A ∈ train ∧
        zA ∈ (Z.model.graphSet A).input_nodes ++
            (Z.model.graphSet A).non_input_nodes ∧
        (Z.model.graphSet A).node_component zA =
            (Z.model.graphSet B).node_component zB ∧
        (Z.model.graphSet A).node_value zA =
            (Z.model.graphSet B).node_value zB ∧
        (M.graphSet A).node_value zA =
            (M.graphSet B).node_value zB := by
  intro zB hzB
  let gB := Z.model.graphSet B
  let full := gB.input_nodes ++ gB.intermediate_nodes ++ gB.output_nodes
  have h_full_eq : full = gB.input_nodes ++ gB.non_input_nodes := by
    rw [Graph.non_input_nodes, ← List.append_assoc]
  -- Define the induction predicate P(n): there exists a training node matching n.
  let P (n : Node) : Prop :=
    ∃ (A : Sample) (zA : Node),
      A ∈ train ∧
      zA ∈ (Z.model.graphSet A).input_nodes ++
          (Z.model.graphSet A).non_input_nodes ∧
      (Z.model.graphSet A).node_component zA = gB.node_component n ∧
      (Z.model.graphSet A).node_value zA = gB.node_value n ∧
      (M.graphSet A).node_value zA = (M.graphSet B).node_value n
  -- It suffices to prove P for all nodes in the full list by induction on index.
  suffices h_all : ∀ i (h : i < full.length), P (full.get ⟨i, h⟩) by
    have h_or : zB ∈ gB.input_nodes ∨ zB ∈ gB.non_input_nodes := by simpa using hzB
    have h_mem : zB ∈ full := by
      rw [h_full_eq]
      rcases h_or with (h | h)
      · rw [List.mem_append]; left; exact h
      · rw [List.mem_append]; right; exact h
    rcases List.mem_iff_get.mp h_mem with ⟨i, hi_eq⟩
    rw [← hi_eq]
    exact h_all i.1 i.2
  -- Strong induction on the index i in the topological order.
  intro i
  refine Nat.strong_induction_on i fun i ih => ?_
  intro h_lt
  let n := full.get ⟨i, h_lt⟩
  by_cases hn_input : n ∈ gB.input_nodes
  · -- Base case: n is an input node, use the base case lemma.
    exact input_node_match_from_noninput Z M h_struct B hB n hn_input
  · -- Inductive step: n is a non-input node.
    have hn_noninput : n ∈ gB.non_input_nodes := by
      have mem_n : n ∈ full := List.get_mem full ⟨i, h_lt⟩
      rw [h_full_eq, List.mem_append] at mem_n
      rcases mem_n with (h | h)
      · exact absurd h hn_input
      · exact h
    have hB_in_all : B ∈ train ++ test := by rw [List.mem_append]; right; exact hB
    obtain ⟨h_input_eq_B, h_inter_eq_B, h_out_eq_B, h_comp_eq_B⟩ := h_struct B hB_in_all
    have h_non_eq_B : (M.graphSet B).non_input_nodes = (Z.model.graphSet B).non_input_nodes := by
      rw [Graph.non_input_nodes, Graph.non_input_nodes]
      congr
    -- For each input m of n, the induction hypothesis provides a matching training node.
    have h_ind_step : ∀ m ∈ gB.node_inputs n,
      ∃ (C : Sample) (zC : Node),
        C ∈ train ∧
        (zC ∈ (Z.model.graphSet C).input_nodes ∨
         zC ∈ (Z.model.graphSet C).non_input_nodes) ∧
        (M.graphSet C).node_component zC = (M.graphSet B).node_component m ∧
        (M.graphSet C).node_value zC = (M.graphSet B).node_value m ∧
        (Z.model.graphSet C).node_value zC = gB.node_value m := by
      intro m hm
      have h_idx_lt := gB.topological_order n hn_noninput m hm
      have h_m_in_full : m ∈ full :=
        gB.input_nodes_in_graph n m hm
      rcases List.mem_iff_get.mp h_m_in_full with ⟨j, hj_eq⟩
      have h_nodup := gB.ordered_nodup
      have hj_lt_i : j.val < i :=
        index_lt_from_topological_order h_nodup m n h_idx_lt j.val j.2 hj_eq i h_lt rfl
      have hP_m : P m := hj_eq ▸ ih j.val hj_lt_i j.2
      rcases hP_m with ⟨C, zC, hC, hzC_append, hcomp_C, hval_C, hvalM_C⟩
      have hzC_or := List.mem_append.mp hzC_append
      have hC_in_all : C ∈ train ++ test := by rw [List.mem_append]; left; exact hC
      obtain ⟨h_input_eq_C, h_inter_eq_C, h_out_eq_C, h_comp_eq_C⟩ := h_struct C hC_in_all
      have h_non_eq_C : (M.graphSet C).non_input_nodes = (Z.model.graphSet C).non_input_nodes := by
        rw [Graph.non_input_nodes, Graph.non_input_nodes]
        congr
      -- Prove that the component of zC in M equals the component of m in M.
      have hcompM_C : (M.graphSet C).node_component zC = (M.graphSet B).node_component m := by
        have hm_in_union : m ∈ gB.input_nodes ++ gB.non_input_nodes := by
          rw [← h_full_eq]
          exact gB.input_nodes_in_graph n m hm
        rcases List.mem_append.1 hm_in_union with (hm_input | hm_noninput)
        · -- m is an input node: both components must be inputComponent.
          have hcompB : (M.graphSet B).node_component m = inputComponent := by
            have hm_in_M_input : m ∈ (M.graphSet B).input_nodes :=
              h_input_eq_B.symm ▸ hm_input
            exact (M.graphSet B).node_component_input m hm_in_M_input
          have hcompC' : (M.graphSet C).node_component zC = inputComponent := by
            rcases hzC_or with (hzC_input | hzC_noninput)
            · have hzC_in_M_input : zC ∈ (M.graphSet C).input_nodes :=
                h_input_eq_C.symm ▸ hzC_input
              exact (M.graphSet C).node_component_input zC hzC_in_M_input
            · exfalso
              have hcomp_m : gB.node_component m = inputComponent :=
                gB.node_component_input m hm_input
              have hcomp_zC : (Z.model.graphSet C).node_component zC = inputComponent :=
                hcomp_C.trans hcomp_m
              have h_not_input := (Z.model.graphSet C).non_input_component_not_input zC hzC_noninput
              rw [hcomp_zC] at h_not_input
              contradiction
          rw [hcompC', hcompB]
        · -- m is a non-input node: use structural alignment.
          have hcompB : (M.graphSet B).node_component m = gB.node_component m :=
            (h_comp_eq_B m (h_non_eq_B ▸ hm_noninput)).1
          rcases hzC_or with (hzC_input | hzC_noninput)
          · -- zC is input but m is non-input: contradiction.
            exfalso
            have h_comp_input : (Z.model.graphSet C).node_component zC = inputComponent :=
              (Z.model.graphSet C).node_component_input zC hzC_input
            have hcomp_m_not_input : gB.node_component m ≠ inputComponent :=
              gB.non_input_component_not_input m hm_noninput
            rw [← hcomp_C] at hcomp_m_not_input
            exact hcomp_m_not_input h_comp_input
          · -- zC is non-input: use structural alignment.
            have hzC_in_M_noninput : zC ∈ (M.graphSet C).non_input_nodes :=
              h_non_eq_C.symm ▸ hzC_noninput
            have hcompC' : (M.graphSet C).node_component zC =
                (Z.model.graphSet C).node_component zC :=
              (h_comp_eq_C zC hzC_in_M_noninput).1
            rw [hcompC', hcomp_C, hcompB]
      -- Now apply the inductive step lemma.
      exact ⟨C, zC, hC, hzC_or, hcompM_C, hvalM_C, hval_C⟩
    -- Obtain A,zA by the inductive_step lemma.
    obtain ⟨A, zA, hA, hzA, hcomp, z_val_eq, m_val_eq⟩ :=
      inductive_step Z M h_struct h_inj B hB n hn_noninput h_ind_step
    have hzA_in_union : zA ∈ (Z.model.graphSet A).input_nodes ++
        (Z.model.graphSet A).non_input_nodes :=
      List.mem_append_right _ hzA
    exact ⟨A, zA, hA, hzA_in_union, hcomp, z_val_eq, m_val_eq⟩

end TACG.Derivations.Sufficiency.InductionOverGraph
