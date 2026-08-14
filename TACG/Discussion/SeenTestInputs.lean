import TACG.Definitions
import TACG.Derivations.Sufficiency.InjectiveComponentOutputs
import TACG.Derivations.Sufficiency.InductionOverGraph
import TACG.Derivations.Sufficiency.ComponentInput

open TACG.Definitions
open TACG.Derivations.Sufficiency.InjectiveComponentOutputs
open TACG.Derivations.Sufficiency.InductionOverGraph
open TACG.Derivations.Sufficiency.ComponentInput

namespace TACG.Discussion.SeenTestInputs

/-!
# Auxiliary Lemma 1: Convert membership in M graph to Z graph
-/
private lemma membership_M_to_Z {train test : List Sample}
    (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (B : Sample) (hB_test : B ∈ test)
    (n : Node) (hn_M : n ∈ (M.graphSet B).non_input_nodes) :
    n ∈ (Z.model.graphSet B).non_input_nodes := by
  obtain ⟨_, h_inter_eq, h_out_eq, _⟩ := h_struct B (by rw [List.mem_append]; right; exact hB_test)
  have h_non_eq : (M.graphSet B).non_input_nodes = (Z.model.graphSet B).non_input_nodes :=
    by simp [Graph.non_input_nodes, h_inter_eq, h_out_eq]
  rw [h_non_eq] at hn_M
  exact hn_M

/-!
# Auxiliary Lemma 2: Build induction hypothesis for each input node of a test node
using induction_over_graph to construct a matching training node.
-/
private lemma build_induction_hypothesis {train test : List Sample}
    (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (h_inj : ∀ c ∈ components_list M train, InjectiveRepresentation c train M Z.model)
    (B : Sample) (hB_test : B ∈ test)
    (n : Node) :
    ∀ (n' : Node) (_ : n' ∈ (Z.model.graphSet B).node_inputs n),
      ∃ (C : Sample) (zC : Node),
        C ∈ train ∧
        (zC ∈ (Z.model.graphSet C).input_nodes ∨ zC ∈ (Z.model.graphSet C).non_input_nodes) ∧
        (M.graphSet C).node_component zC = (M.graphSet B).node_component n' ∧
        (M.graphSet C).node_value zC = (M.graphSet B).node_value n' ∧
        (Z.model.graphSet C).node_value zC = (Z.model.graphSet B).node_value n' := by
  let gB_Z := Z.model.graphSet B
  let gB_M := M.graphSet B
  intro n' hn'_input
  have n'_in_union_append : n' ∈ gB_Z.input_nodes ++ gB_Z.non_input_nodes :=
    by rw [Graph.non_input_nodes, ← List.append_assoc]; exact
    gB_Z.input_nodes_in_graph n n' hn'_input
  have n'_in_union_set : n' ∈ gB_Z.input_nodes ∪ gB_Z.non_input_nodes := by
    rw [List.mem_union_iff]
    exact List.mem_append.mp n'_in_union_append
  obtain ⟨C, zC, hC, hzC_in_union, hcomp_Z, hval_Z, hval_M⟩ :=
    induction_over_graph Z M h_struct h_inj B hB_test n' n'_in_union_set
  have hC_in_all : C ∈ train ++ test := by rw [List.mem_append]; left; exact hC
  obtain ⟨h_input_eq_C, h_inter_eq_C, h_out_eq_C, h_comp_eq_C⟩ := h_struct C hC_in_all
  have h_non_eq_C : (M.graphSet C).non_input_nodes = (Z.model.graphSet C).non_input_nodes :=
    by simp [Graph.non_input_nodes, h_inter_eq_C, h_out_eq_C]
  obtain ⟨h_input_eq_B, h_inter_eq_B, h_out_eq_B, h_comp_eq_B⟩ :=
    h_struct B (by rw [List.mem_append]; right; exact hB_test)
  have h_non_eq_B : (M.graphSet B).non_input_nodes = (Z.model.graphSet B).non_input_nodes :=
    by simp [Graph.non_input_nodes, h_inter_eq_B, h_out_eq_B]
  have n'_mem_union : n' ∈ gB_Z.input_nodes ++ gB_Z.non_input_nodes :=
    by rw [Graph.non_input_nodes, ← List.append_assoc]; exact
    gB_Z.input_nodes_in_graph n n' hn'_input
  rcases List.mem_append.mp n'_mem_union with (hn'_input_node | hn'_noninput_node)
  · -- n' is an input node: both components must be inputComponent.
    have hcomp_n'_Z : gB_Z.node_component n' = inputComponent :=
      gB_Z.node_component_input n' hn'_input_node
    rw [hcomp_n'_Z] at hcomp_Z
    have hzC_input : zC ∈ (Z.model.graphSet C).input_nodes := by
      rcases List.mem_append.mp hzC_in_union with (hzC_input | hzC_noninput)
      · exact hzC_input
      · exfalso
        apply (Z.model.graphSet C).non_input_component_not_input zC hzC_noninput
        rw [hcomp_Z]
    rw [← h_input_eq_C] at hzC_input
    rw [← h_input_eq_B] at hn'_input_node
    have hcomp_C_M : (M.graphSet C).node_component zC = inputComponent :=
      (M.graphSet C).node_component_input zC hzC_input
    have hcomp_n'_M : gB_M.node_component n' = inputComponent :=
      gB_M.node_component_input n' hn'_input_node
    have hcomp_eq : (M.graphSet C).node_component zC = gB_M.node_component n' := by
      rw [hcomp_C_M, hcomp_n'_M]
    exact ⟨C, zC, hC, List.mem_append.mp hzC_in_union, hcomp_eq, hval_M, hval_Z⟩
  · -- n' is a non-input node: use structural alignment to transfer component equality.
    have hcomp_n'_Z : gB_Z.node_component n' ≠ inputComponent :=
      gB_Z.non_input_component_not_input n' hn'_noninput_node
    rw [← hcomp_Z] at hcomp_n'_Z
    have hzC_noninput : zC ∈ (Z.model.graphSet C).non_input_nodes := by
      rcases List.mem_append.mp hzC_in_union with (hzC_input | hzC_noninput)
      · exfalso
        have h_comp_input : (Z.model.graphSet C).node_component zC = inputComponent :=
          (Z.model.graphSet C).node_component_input zC hzC_input
        rw [h_comp_input] at hcomp_n'_Z
        contradiction
      · exact hzC_noninput
    have hzC_non_M := h_non_eq_C.symm ▸ hzC_noninput
    have hcomp_C_M : (M.graphSet C).node_component zC =
        (Z.model.graphSet C).node_component zC :=
      (h_comp_eq_C zC hzC_non_M).1
    have hn'_non_M := h_non_eq_B.symm ▸ hn'_noninput_node
    have hcomp_n'_M : gB_M.node_component n' =
        gB_Z.node_component n' :=
      (h_comp_eq_B n' hn'_non_M).1
    have hcomp_eq : (M.graphSet C).node_component zC = gB_M.node_component n' :=
      by rw [hcomp_C_M, hcomp_Z, hcomp_n'_M]
    exact ⟨C, zC, hC, List.mem_append.mp hzC_in_union, hcomp_eq, hval_M, hval_Z⟩

/-!
# Auxiliary Lemma 3: Convert non-input membership from Z graph to M graph
-/
private lemma z_to_m_membership {train test : List Sample}
    (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (A : Sample) (hA : A ∈ train)
    (zA : Node) (hzA_non_Z : zA ∈ (Z.model.graphSet A).non_input_nodes) :
    zA ∈ (M.graphSet A).non_input_nodes := by
  obtain ⟨_, h_inter_eq, h_out_eq, _⟩ := h_struct A (by rw [List.mem_append]; left; exact hA)
  have h_non_eq : (M.graphSet A).non_input_nodes = (Z.model.graphSet A).non_input_nodes :=
    by simp [Graph.non_input_nodes, h_inter_eq, h_out_eq]
  rwa [← h_non_eq] at hzA_non_Z

/-!
# Auxiliary Lemma 4: Transfer component equality from Z graph to M graph
-/
private lemma z_to_m_component_eq {train test : List Sample}
    (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (A : Sample) (hA : A ∈ train)
    (B : Sample) (hB_test : B ∈ test)
    (zA : Node) (n : Node)
    (hzA_non_M : zA ∈ (M.graphSet A).non_input_nodes)
    (hn_M : n ∈ (M.graphSet B).non_input_nodes)
    (hcomp_Z : (Z.model.graphSet A).node_component zA = (Z.model.graphSet B).node_component n) :
    (M.graphSet A).node_component zA = (M.graphSet B).node_component n := by
  obtain ⟨_, _, _, h_comp_eq_A⟩ := h_struct A (by rw [List.mem_append]; left; exact hA)
  obtain ⟨_, _, _, h_comp_eq_B⟩ := h_struct B (by rw [List.mem_append]; right; exact hB_test)
  have hcomp_A_eq : (M.graphSet A).node_component zA = (Z.model.graphSet A).node_component zA :=
    (h_comp_eq_A zA hzA_non_M).1
  have hcomp_B_eq : (M.graphSet B).node_component n = (Z.model.graphSet B).node_component n :=
    (h_comp_eq_B n hn_M).1
  rw [hcomp_A_eq, hcomp_B_eq, hcomp_Z]

/-!
# Auxiliary Lemma 5: Prove pointwise component equality on Z graph input lists
-/
private lemma pointwise_comp_eq_on_Z_lists {train test : List Sample}
    (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (A : Sample) (hA : A ∈ train)
    (zA : Node)
    (h_comp_eq_A : ∀ n ∈ (M.graphSet A).non_input_nodes,
      (M.graphSet A).node_component n = (Z.model.graphSet A).node_component n ∧
      (M.graphSet A).node_inputs n = (Z.model.graphSet A).node_inputs n) :
    ∀ x ∈ (Z.model.graphSet A).node_inputs zA,
      (M.graphSet A).node_component x = (Z.model.graphSet A).node_component x := by
  intro x hx
  have hx_in_graph : x ∈ (Z.model.graphSet A).input_nodes ++ (Z.model.graphSet A).non_input_nodes :=
    by rw [Graph.non_input_nodes, ← List.append_assoc]; exact
    (Z.model.graphSet A).input_nodes_in_graph zA x hx
  rcases List.mem_append.mp hx_in_graph with (hx_input | hx_noninput)
  · have hcomp_x_Z : (Z.model.graphSet A).node_component x = inputComponent :=
      (Z.model.graphSet A).node_component_input x hx_input
    obtain ⟨h_input_eq_A, _, _, _⟩ := h_struct A (by rw [List.mem_append]; left; exact hA)
    have hcomp_x_M : (M.graphSet A).node_component x = inputComponent :=
      (M.graphSet A).node_component_input x (h_input_eq_A.symm ▸ hx_input)
    rw [hcomp_x_M, hcomp_x_Z]
  · obtain ⟨_, h_inter_eq_A, h_out_eq_A, _⟩ := h_struct A (by rw [List.mem_append]; left; exact hA)
    have h_non_eq_A : (M.graphSet A).non_input_nodes = (Z.model.graphSet A).non_input_nodes :=
      by simp [Graph.non_input_nodes, h_inter_eq_A, h_out_eq_A]
    have hx_non_M : x ∈ (M.graphSet A).non_input_nodes := h_non_eq_A.symm ▸ hx_noninput
    exact (h_comp_eq_A x hx_non_M).1

/-!
# Auxiliary Lemma 6: From pointwise equality derive list map equality
-/
private lemma map_eq_from_pointwise {α β : Type} (xs : List α) (f g : α → β)
    (h : ∀ x ∈ xs, f x = g x) :
    List.map f xs = List.map g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ a ∈ xs, f a = g a := by
        intro a ha
        exact h a (by simp [ha])
      simp [hx, ih hxs]

/-!
# Auxiliary Lemma 7: Transfer input components list equality from Z graph to M graph
-/
private lemma hcomps_Z_to_hcomps_M {train test : List Sample}
    (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (A : Sample) (hA : A ∈ train)
    (B : Sample) (hB_test : B ∈ test)
    (zA : Node) (n : Node)
    (hzA_non_M : zA ∈ (M.graphSet A).non_input_nodes)
    (hn_M : n ∈ (M.graphSet B).non_input_nodes)
    (hcomps_Z : input_components (Z.model.graphSet A) zA =
                input_components (Z.model.graphSet B) n) :
    input_components (M.graphSet A) zA =
    input_components (M.graphSet B) n := by
  obtain ⟨_, _, _, h_comp_eq_A⟩ := h_struct A (by rw [List.mem_append]; left; exact hA)
  obtain ⟨_, _, _, h_comp_eq_B⟩ := h_struct B (by rw [List.mem_append]; right; exact hB_test)
  have h_inputs_A_eq : (M.graphSet A).node_inputs zA = (Z.model.graphSet A).node_inputs zA :=
    (h_comp_eq_A zA hzA_non_M).2
  have h_inputs_B_eq : (M.graphSet B).node_inputs n = (Z.model.graphSet B).node_inputs n :=
    (h_comp_eq_B n hn_M).2
  -- Pointwise component equality for input lists of A and B.
  have h_comp_map_A_Z := pointwise_comp_eq_on_Z_lists Z M h_struct A hA zA h_comp_eq_A
  have h_comp_map_B_Z : ∀ x ∈ (Z.model.graphSet B).node_inputs n,
      (M.graphSet B).node_component x = (Z.model.graphSet B).node_component x := by
    intro x hx
    have hx_in_graph :
      x ∈ (Z.model.graphSet B).input_nodes ++ (Z.model.graphSet B).non_input_nodes :=
      by rw [Graph.non_input_nodes, ← List.append_assoc]; exact
      (Z.model.graphSet B).input_nodes_in_graph n x hx
    rcases List.mem_append.mp hx_in_graph with (hx_input | hx_noninput)
    · have hcomp_x_Z : (Z.model.graphSet B).node_component x = inputComponent :=
        (Z.model.graphSet B).node_component_input x hx_input
      obtain ⟨h_input_eq_B, _, _, _⟩ := h_struct B (by rw [List.mem_append]; right; exact hB_test)
      have hcomp_x_M : (M.graphSet B).node_component x = inputComponent :=
        (M.graphSet B).node_component_input x (h_input_eq_B.symm ▸ hx_input)
      rw [hcomp_x_M, hcomp_x_Z]
    · obtain ⟨_, h_inter_eq_B, h_out_eq_B, _⟩ :=
          h_struct B (by rw [List.mem_append]; right; exact hB_test)
      have h_non_eq_B : (M.graphSet B).non_input_nodes = (Z.model.graphSet B).non_input_nodes :=
        by simp [Graph.non_input_nodes, h_inter_eq_B, h_out_eq_B]
      have hx_non_M : x ∈ (M.graphSet B).non_input_nodes := h_non_eq_B.symm ▸ hx_noninput
      exact (h_comp_eq_B x hx_non_M).1
  -- Use map_eq_from_pointwise to rewrite the component lists.
  have hA_map_eq : List.map (M.graphSet A).node_component ((Z.model.graphSet A).node_inputs zA) =
                   List.map (Z.model.graphSet A).node_component
                   ((Z.model.graphSet A).node_inputs zA) :=
    map_eq_from_pointwise _ _ _ h_comp_map_A_Z
  have hB_map_eq : List.map (M.graphSet B).node_component ((Z.model.graphSet B).node_inputs n) =
                   List.map (Z.model.graphSet B).node_component
                   ((Z.model.graphSet B).node_inputs n) :=
    map_eq_from_pointwise _ _ _ h_comp_map_B_Z
  -- Combine to prove the final equality.
  unfold input_components
  rw [h_inputs_A_eq, h_inputs_B_eq]
  rw [hA_map_eq, hB_map_eq]
  exact hcomps_Z

/-!
# Main Lemma: Acquire Seen Inputs (Lemma 15 in the paper)

Given structural alignment, and for all used components both unambiguous and
minimized representations hold, then all test component inputs have been seen
in training. This is used in the alternative version of the theorem to derive
the seen-inputs condition from AS-UMR.
-/
lemma seen_test_inputs {train test : List Sample}
    (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (h_unamb : ∀ c ∈ components_list M train, UnambiguousRepresentation c train M Z.model)
    (h_min : ∀ c ∈ components_list M train, MinimizedRepresentation c train M Z.model) :
    seen_inputs_condition M train test := by
  unfold seen_inputs_condition
  refine fun B hB_test n hn_M => ?_
  let gB_Z := Z.model.graphSet B
  let gB_M := M.graphSet B
  -- 1. Convert M graph membership to Z graph.
  have hn_Z := membership_M_to_Z Z M h_struct B hB_test n hn_M
  -- 2. From unamb and min, derive injective representation for all used components.
  have inj_repr : ∀ c ∈ components_list M train,
  InjectiveRepresentation c train M Z.model := by
    intro c hc
    have h_struct_train : StructuralAlignment M Z.model train := by
      intro s hs
      exact h_struct s (List.mem_append_left test hs)
    exact injective_component_outputs M Z.model train c h_struct_train (h_unamb c hc) (h_min c hc)
  -- 3. Build the induction hypothesis for the inputs of n.
  have ind_hyp := build_induction_hypothesis Z M h_struct inj_repr B hB_test n
  -- 4. Apply Lemma 11 (Component Input) to obtain matching inputs.
  obtain ⟨A, zA, hA, hzA_non_Z, hcomp_Z, hvals_Z, hcomps_Z, hvals_M⟩ :=
    component_input Z M h_struct inj_repr B hB_test n hn_Z ind_hyp
  -- 5. Convert the witness from Z graph to M graph.
  have hzA_non_M := z_to_m_membership Z M h_struct A hA zA hzA_non_Z
  have hcomp_M := z_to_m_component_eq Z M h_struct A hA B hB_test zA n hzA_non_M hn_M hcomp_Z
  have hcomps_M := hcomps_Z_to_hcomps_M Z M h_struct A hA B hB_test zA n hzA_non_M hn_M hcomps_Z
  -- 6. Construct the final witness for seen_inputs_condition.
  refine ⟨A, hA, zA, hzA_non_M, hcomp_M, hvals_M, hcomps_M⟩

end TACG.Discussion.SeenTestInputs
