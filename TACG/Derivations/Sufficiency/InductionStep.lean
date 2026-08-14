import TACG.Definitions
import TACG.Derivations.Sufficiency.ComponentInput

open TACG.Definitions
open TACG.Derivations.Sufficiency.ComponentInput

namespace TACG.Derivations.Sufficiency.InductionStep

/-- Lemma: Induction Step (Lemma 6 in the paper).
    Given structural alignment and injective representation for all used
    non-output components, if for every input node of a test node zB there is
    a training node matching it in both reference and hypothesis values,
    then there exists a training node zA that matches zB in component,
    reference value, and hypothesis value.
    This is the core inductive step for proving sufficiency. -/
lemma induction_step
    {train test : List Sample} (Z : ReferenceModel train test) (M : Model)
    (h_struct : StructuralAlignment M Z.model (train ++ test))
    (h_inj : ∀ c ∈ components_list M train, -- only require components used in training
      InjectiveRepresentation c train M Z.model)
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
      (Z.model.graphSet A).node_value zA = (Z.model.graphSet B).node_value zB ∧
      (M.graphSet A).node_value zA = (M.graphSet B).node_value zB := by
  -- First, obtain a training node zA whose inputs match zB in reference and hypothesis.
  obtain ⟨A, zA, hA, hzA, hcomp, hmatch⟩ :=
    component_input Z M h_struct h_inj B hB zB zB_in h_ind
  have hvals := hmatch.1          -- reference input values match
  have hcomps := hmatch.2.1       -- reference input components match
  have hM_vals := hmatch.2.2      -- hypothesis input values match
  -- Structural alignment gives us equality of non-input node lists and component mappings.
  have hA_in_all : A ∈ train ++ test := by rw [List.mem_append]; left; exact hA
  have hB_in_all : B ∈ train ++ test := by rw [List.mem_append]; right; exact hB
  obtain ⟨h_input_eq_A, h_inter_eq_A, h_out_eq_A, h_comp_eq_A⟩ := h_struct A hA_in_all
  obtain ⟨h_input_eq_B, h_inter_eq_B, h_out_eq_B, h_comp_eq_B⟩ := h_struct B hB_in_all
  have h_non_eq_A : (M.graphSet A).non_input_nodes = (Z.model.graphSet A).non_input_nodes := by
    rw [Graph.non_input_nodes, Graph.non_input_nodes]
    congr
  have h_non_eq_B : (M.graphSet B).non_input_nodes = (Z.model.graphSet B).non_input_nodes := by
    rw [Graph.non_input_nodes, Graph.non_input_nodes]
    congr
  have zA_in_M : zA ∈ (M.graphSet A).non_input_nodes :=
    h_non_eq_A.symm ▸ hzA
  have zB_in_M : zB ∈ (M.graphSet B).non_input_nodes :=
    h_non_eq_B.symm ▸ zB_in
  -- Component equality in M follows from structural alignment and hcomp.
  have comp_M_A : (M.graphSet A).node_component zA = (Z.model.graphSet A).node_component zA :=
    (h_comp_eq_A zA zA_in_M).1
  have comp_M_B : (M.graphSet B).node_component zB = (Z.model.graphSet B).node_component zB :=
    (h_comp_eq_B zB zB_in_M).1
  -- Reference values are equal by deterministic computation of the reference model.
  have z_val_eq : (Z.model.graphSet A).node_value zA = (Z.model.graphSet B).node_value zB := by
    rw [Z.model.comp_valuation A zA hzA]
    rw [hcomp]
    simp only [input_values] at hvals
    rw [hvals]
    rw [← Z.model.comp_valuation B zB zB_in]
  -- Hypothesis values are equal by deterministic computation of the model M.
  have m_val_eq : (M.graphSet A).node_value zA = (M.graphSet B).node_value zB := by
    have comp_eq_M : (M.graphSet A).node_component zA = (M.graphSet B).node_component zB := by
      rw [comp_M_A, hcomp, comp_M_B.symm]
    rw [M.comp_valuation A zA zA_in_M]
    rw [comp_eq_M]
    simp only [input_values] at hM_vals
    rw [hM_vals]
    rw [← M.comp_valuation B zB zB_in_M]
  -- Package all the equalities into the conclusion.
  exact ⟨A, zA, hA, hzA, hcomp, z_val_eq, m_val_eq⟩

end TACG.Derivations.Sufficiency.InductionStep
