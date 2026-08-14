import TACG.Definitions
import TACG.Derivations.Sufficiency.SurjectiveMapping
import TACG.Derivations.MathematicalPreliminaries.MappingsOnNodes
import TACG.Derivations.Helper.SetMembership

open TACG.Definitions
open TACG.Derivations.Sufficiency.SurjectiveMapping
open TACG.Derivations.MathematicalPreliminaries.MappingsOnNodes
open TACG.Derivations.Helper.SetMembership

namespace TACG.Derivations.Sufficiency.InjectiveComponentOutputs

/-- If (h,z) satisfies the ξ relation, then h is in M's ξ_set,
    because ξ only involves intermediate nodes. -/
private lemma hyp_in_ξ_set_of_ξ {M Z : Model} {train : List Sample} {c : Component}
    {h z : Value} (rel : ξ M Z train c h z) : h ∈ ξ_set M train c := by
  rcases rel with ⟨A, hA, out, h_out_M, h_comp_M, h_eq, _⟩
  -- By definition of ξ, out is an intermediate node.
  unfold ξ_set
  rw [mem_toFinset, List.mem_dedup, List.mem_flatten]
  let L' := List.map (fun out' => (M.graphSet A).node_value out')
               (List.filter (fun out' => (M.graphSet A).node_component out' = c)
                 (M.graphSet A).intermediate_nodes)
  refine ⟨L', ?_, ?_⟩
  · rw [List.mem_map]; exact ⟨A, hA, rfl⟩
  · rw [List.mem_map]; use out; constructor
    · rw [List.mem_filter]; exact ⟨h_out_M, by simp [h_comp_M]⟩
    · exact h_eq

/-- If (h,z) satisfies the ξ relation, then z is in Z's ξ_set,
    using structural alignment to transfer intermediate node membership. -/
private lemma value_in_ξ_set_of_ξ {M Z : Model} {train : List Sample} {c : Component}
    (h_struct : StructuralAlignment M Z train)
    {h z : Value} (rel : ξ M Z train c h z) : z ∈ ξ_set Z train c := by
  rcases rel with ⟨A, hA, out, h_out_M, h_comp_M, _, z_eq⟩
  obtain ⟨_, h_inter_eq, _, h_comp_eq⟩ := h_struct A hA
  -- Structural alignment gives equal intermediate node lists, so out is also in Z.
  have out_in_Z : out ∈ (Z.graphSet A).intermediate_nodes := by
    rw [← h_inter_eq]; exact h_out_M
  -- The component is also the same.
  have comp_in_Z : (Z.graphSet A).node_component out = c := by
    have h_out_M_non : out ∈ (M.graphSet A).non_input_nodes := by
      simp [Graph.non_input_nodes, h_out_M]
    rw [← (h_comp_eq out h_out_M_non).1]; exact h_comp_M
  -- Construct membership proof for Z's ξ_set.
  unfold ξ_set
  rw [mem_toFinset, List.mem_dedup, List.mem_flatten]
  let L' := List.map (fun out' => (Z.graphSet A).node_value out')
               (List.filter (fun out' => (Z.graphSet A).node_component out' = c)
                 (Z.graphSet A).intermediate_nodes)
  refine ⟨L', ?_, ?_⟩
  · rw [List.mem_map]; exact ⟨A, hA, rfl⟩
  · rw [List.mem_map]; use out; constructor
    · rw [List.mem_filter]; exact ⟨out_in_Z, by simp [comp_in_Z]⟩
    · exact z_eq

/--
Auxiliary function: given a hypothesis value h (known to be in M's ξ_set),
use unambiguity (unique correspondence) and structural alignment to construct
a unique reference value z, along with z ∈ ξ_set Z and the ξ relation.
-/
noncomputable def get_z (M Z : Model) (train : List Sample) (c : Component)
    (h_struct : StructuralAlignment M Z train)
    (_h_unamb : UnambiguousRepresentation c train M Z)
    (h : Value) (h_in_dom : h ∈ ξ_set M train c) :
    {z : Value // z ∈ ξ_set Z train c ∧ ξ M Z train c h z} := by
  -- Extract a concrete intermediate node out from h ∈ ξ_set M.
  let ex1 := ξ_set_mem_elim M train c h h_in_dom
  let A := Classical.choose ex1
  have hA : A ∈ train := (Classical.choose_spec ex1).1
  let ex2 := (Classical.choose_spec ex1).2
  let out := Classical.choose ex2
  have h_out_M : out ∈ (M.graphSet A).intermediate_nodes := (Classical.choose_spec ex2).1
  have h_comp_M : (M.graphSet A).node_component out = c := (Classical.choose_spec ex2).2.1
  have h_eq : (M.graphSet A).node_value out = h := (Classical.choose_spec ex2).2.2
  -- Structural alignment ensures the corresponding intermediate node exists in Z.
  obtain ⟨_, h_inter_eq, _, h_comp_eq⟩ := h_struct A hA
  have out_in_Z : out ∈ (Z.graphSet A).intermediate_nodes := by
    rw [← h_inter_eq]; exact h_out_M
  have comp_in_Z : (Z.graphSet A).node_component out = c := by
    have h_out_non : out ∈ (M.graphSet A).non_input_nodes := by
      simp [Graph.non_input_nodes, h_out_M]
    rw [← (h_comp_eq out h_out_non).1]; exact h_comp_M
  -- Take the value of the same node in Z as z0.
  let z0 := (Z.graphSet A).node_value out
  have ξ_proof : ξ M Z train c h z0 :=
    ⟨A, hA, out, h_out_M, h_comp_M, h_eq, rfl⟩
  have z0_in_img := value_in_ξ_set_of_ξ h_struct ξ_proof
  exact Subtype.mk z0 (And.intro z0_in_img ξ_proof)

/--
Lemma 7 (Injective Component Outputs):
If M is structurally aligned with Z, and for component c we have both
unambiguous and minimized representations, then M has an injective
representation on c (i.e., ξ_c is injective).
-/
lemma injective_component_outputs (M Z : Model) (train : List Sample) (c : Component)
    (h_struct : StructuralAlignment M Z train)
    (h_unamb : UnambiguousRepresentation c train M Z)
    (h_min : MinimizedRepresentation c train M Z) :
    InjectiveRepresentation c train M Z := by
  unfold InjectiveRepresentation
  intros z z_in h1 h2 rel1 rel2
  have h1_in := hyp_in_ξ_set_of_ξ rel1
  have h2_in := hyp_in_ξ_set_of_ξ rel2
  let dom := ξ_set M train c
  let img := ξ_set Z train c
  haveI : Fintype {x // x ∈ dom} := Fintype.ofFinset dom (by simp)
  haveI : Fintype {y // y ∈ img} := Fintype.ofFinset img (by simp)
  -- Construct a mapping f from dom to img using get_z and surjective_mapping.
  let f (x : {x // x ∈ dom}) : {y // y ∈ img} :=
    let w := get_z M Z train c h_struct h_unamb x.val x.property
    Subtype.mk w.val w.property.1
  have f_surj : Function.Surjective f := by
    intro ⟨y, y_in⟩
    obtain ⟨h, h_in_dom, ξ⟩ := surjective_mapping M Z train h_struct c y y_in
    let x : {x // x ∈ dom} := ⟨h, h_in_dom⟩
    have f_eq : f x = ⟨y, y_in⟩ := by
      dsimp [f]
      let w := get_z M Z train c h_struct h_unamb h h_in_dom
      apply Subtype.ext
      exact h_unamb h h_in_dom w.val y w.property.2 ξ
    exact ⟨x, f_eq⟩
  -- Minimized representation gives |dom| = |img|, hence equal finite cardinalities.
  have card_eq : Fintype.card {x // x ∈ dom} = Fintype.card {y // y ∈ img} := by
    have h1 : Fintype.card {x // x ∈ dom} = dom.card := by simp
    have h2 : Fintype.card {y // y ∈ img} = img.card := by simp
    rw [h1, h2, h_min]
  -- Apply cardinality lemma: surjective with equal cardinalities ⇒ injective.
  have f_inj := (mappings_on_nodes f f_surj).mpr card_eq
  let h1_sub : {x // x ∈ dom} := ⟨h1, h1_in⟩
  let h2_sub : {x // x ∈ dom} := ⟨h2, h2_in⟩
  have eq1 : f h1_sub = ⟨z, z_in⟩ := by
    dsimp [f]
    let w := get_z M Z train c h_struct h_unamb h1 h1_in
    apply Subtype.ext
    exact h_unamb h1 h1_in w.val z w.property.2 rel1
  have eq2 : f h2_sub = ⟨z, z_in⟩ := by
    dsimp [f]
    let w := get_z M Z train c h_struct h_unamb h2 h2_in
    apply Subtype.ext
    exact h_unamb h2 h2_in w.val z w.property.2 rel2
  have f_eq : f h1_sub = f h2_sub := by rw [eq1, eq2]
  have h_sub_eq := f_inj f_eq
  exact congr_arg Subtype.val h_sub_eq

end TACG.Derivations.Sufficiency.InjectiveComponentOutputs
