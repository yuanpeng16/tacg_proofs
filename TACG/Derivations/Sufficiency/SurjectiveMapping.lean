import TACG.Definitions
import TACG.Derivations.Helper.SetMembership

open TACG.Definitions
open TACG.Derivations.Helper.SetMembership

namespace TACG.Derivations.Sufficiency.SurjectiveMapping

/-- Lemma 6 (Surjective Mapping) from the paper.
    If M and Z are structurally aligned on training set `train`, then for any component c,
    every reference value z_val produced by Z on a training sample has a corresponding
    hypothesis value h_val in M from the same sample and node, such that h_val is in
    M's ξ_set and ξ relates h_val to z_val.

    Proof sketch:
    1. Use ξ_set_mem_elim to extract a training sample A and node out from Z's graph
       with intermediate node, component c, and value z_val.
    2. Structural alignment gives that out is also an intermediate node in M's graph,
       with the same component.
    3. Take h_val = M.graphSet A.node_value out. Then ξ holds by construction.
    4. Construct the membership proof for h_val ∈ ξ_set M train c.
-/
lemma surjective_mapping (M Z : Model) (train : List Sample)
    (h_struct : StructuralAlignment M Z train)
    (c : Component) (z_val : Value)
    (h_in_img : z_val ∈ ξ_set Z train c) :
    ∃ h_val : Value, h_val ∈ ξ_set M train c ∧ ξ M Z train c h_val z_val := by
  obtain ⟨A, hA, out, h_outZ, h_compZ, h_z⟩ := ξ_set_mem_elim Z train c z_val h_in_img
  specialize h_struct A hA
  obtain ⟨_, h_inter_eq, _, h_comp_eq⟩ := h_struct
  -- Equal intermediate node lists imply out is also in M's intermediate nodes.
  have h_outM : out ∈ (M.graphSet A).intermediate_nodes := by
    rw [h_inter_eq]
    exact h_outZ
  -- Structural alignment ensures component equality for intermediate nodes.
  have h_outM_non : out ∈ (M.graphSet A).non_input_nodes := by
    simp [Graph.non_input_nodes, h_outM]
  have h_compM : (M.graphSet A).node_component out = c := by
    rw [(h_comp_eq out h_outM_non).1]
    exact h_compZ
  let h_val := (M.graphSet A).node_value out
  -- Prove h_val belongs to M's ξ_set (based solely on intermediate nodes).
  have h_dom : h_val ∈ ξ_set M train c := by
    unfold ξ_set
    rw [mem_toFinset, List.mem_dedup, List.mem_flatten]
    -- Construct the sublist containing h_val.
    let L' := List.map (fun out' => (M.graphSet A).node_value out')
                (List.filter (fun out' => (M.graphSet A).node_component out' = c)
                  (M.graphSet A).intermediate_nodes)
    refine ⟨L', ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨A, hA, rfl⟩
    · rw [List.mem_map]
      use out
      constructor
      · rw [List.mem_filter]
        exact ⟨h_outM, by simp [h_compM]⟩
      · rfl
  -- Construct the ξ relation.
  have h_ξ : ξ M Z train c h_val z_val :=
    ⟨A, hA, out, h_outM, h_compM, rfl, h_z⟩
  exact ⟨h_val, h_dom, h_ξ⟩

end TACG.Derivations.Sufficiency.SurjectiveMapping
