import Mathlib.Analysis.SpecialFunctions.Log.Basic

import TACG.Definitions
import TACG.Derivations.Sufficiency.SurjectiveMapping
import TACG.Derivations.Helper.SetMembership

open Finset
open TACG.Definitions
open TACG.Derivations.Sufficiency.SurjectiveMapping
open TACG.Derivations.Helper.SetMembership

namespace TACG.ExampleApproach.MinimumEntropyImpliesMinimizedRepresentationHelper

/-! ### Auxiliary lemma: node value in ξ_set (using intermediate_nodes) -/

/-- If an intermediate node in Z has component c, its value belongs to ξ_set Z train c. -/
private lemma node_value_in_ξ_set (Z : Model) (train : List Sample) (c : Component)
    (A : Sample) (hA : A ∈ train) (n : Node) (h_in : n ∈ (Z.graphSet A).intermediate_nodes)
    (h_comp : (Z.graphSet A).node_component n = c) :
    (Z.graphSet A).node_value n ∈ ξ_set Z train c := by
  unfold ξ_set
  apply List.mem_toFinset.mpr
  apply List.mem_flatten.mpr
  let L := List.map (fun out => (Z.graphSet A).node_value out)
            (List.filter (fun out => decide ((Z.graphSet A).node_component out = c))
              (Z.graphSet A).intermediate_nodes)
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

/-! ## Auxiliary Lemma 1: Unique existence -/

/-- For each hypothesis value h ∈ ξ_set M train c, there exists a unique reference
    value z ∈ ξ_set Z train c such that ξ M Z train c h z holds.
    This follows from unambiguous representation and structural alignment. -/
lemma exists_unique_mapping
    (M Z : Model) (train : List Sample) (c : Component)
    (h_struct : StructuralAlignment M Z train)
    (h_unambig : UnambiguousRepresentation c train M Z)
    (h : Value) (h_in_D : h ∈ ξ_set M train c) :
    ∃! z, z ∈ ξ_set Z train c ∧ ξ M Z train c h z :=
by
  let R := ξ_set Z train c
  -- Extract a node from the ξ_set membership, which gives intermediate_nodes proof.
  rcases ξ_set_mem_elim M train c h h_in_D with ⟨A, hA, out, h_outM_inter, h_compM, h_eqM⟩
  obtain ⟨h_input_eq, h_inter_eq, h_out_eq, h_comp_eq⟩ := h_struct A hA
  -- Lift intermediate_nodes to non_input_nodes for use with h_comp_eq.
  have h_outM : out ∈ (M.graphSet A).non_input_nodes := by
    rw [Graph.non_input_nodes]
    exact List.mem_append_left (M.graphSet A).output_nodes h_outM_inter
  -- Use StructuralAlignment to get component equality in Z.
  have h_compZ : (Z.graphSet A).node_component out = c :=
    ((h_comp_eq out h_outM).1) ▸ h_compM
  -- Construct intermediate_nodes proof in Z for node_value_in_ξ_set.
  have h_outZ_inter : out ∈ (Z.graphSet A).intermediate_nodes := h_inter_eq ▸ h_outM_inter
  let z := (Z.graphSet A).node_value out
  have h_z_in_R : z ∈ R := node_value_in_ξ_set Z train c A hA out h_outZ_inter h_compZ
  -- Construct the ξ relation using the intermediate proof.
  have h_ξ : ξ M Z train c h z := ⟨A, hA, out, h_outM_inter, h_compM, h_eqM, rfl⟩
  refine ⟨z, ⟨h_z_in_R, h_ξ⟩, fun z' ⟨_, hξ'⟩ => Eq.symm (h_unambig h h_in_D z z' h_ξ hξ')⟩

/-! ## Auxiliary Lemma 2: Construct surjective g -/

/-- Define g : D' → R' mapping each hypothesis value to its unique reference value.
    This mapping is surjective by the surjective_mapping lemma. -/
lemma surjective_g
    (M Z : Model) (train : List Sample) (c : Component)
    (h_struct : StructuralAlignment M Z train)
    (D : Finset Value) (R : Finset Value)
    (h_D_eq : D = ξ_set M train c)
    (h_R_eq : R = ξ_set Z train c)
    (h_exists_unique : ∀ h ∈ D, ∃! z ∈ R, ξ M Z train c h z) :
    let D' := {h : Value // h ∈ D}
    let R' := {z : Value // z ∈ R}
    ∃ g : D' → R',
      (∀ h' : D', g h' = ⟨Classical.choose (h_exists_unique h'.val h'.property).exists,
                        (Classical.choose_spec (h_exists_unique h'.val h'.property).exists).1⟩) ∧
      (∀ (r : Value) (r_in_R : r ∈ R), ∃ h' : D', g h' = ⟨r, r_in_R⟩) :=
by
  let D' := {h : Value // h ∈ D}
  let R' := {z : Value // z ∈ R}
  let g (h : D') : R' :=
    let h_val := h.val
    let h_prop := h.property
    let unique := h_exists_unique h_val h_prop
    let z := Classical.choose (unique.exists)
    have h_z_in_R := (Classical.choose_spec (unique.exists)).1
    ⟨z, h_z_in_R⟩
  have h_surj : ∀ (r : Value) (r_in_R : r ∈ R), ∃ h' : D', g h' = ⟨r, r_in_R⟩ := by
    intro r r_in_R
    have r_in_Z : r ∈ ξ_set Z train c := by rw [← h_R_eq]; exact r_in_R
    rcases surjective_mapping M Z train h_struct c r r_in_Z with ⟨h_val, h_in_D, hξ⟩
    have h_in_D' : h_val ∈ D := h_D_eq ▸ h_in_D
    let h' : D' := ⟨h_val, h_in_D'⟩
    have h_eq : g h' = ⟨r, r_in_R⟩ := by
      dsimp [g]
      let unique := h_exists_unique h_val h_in_D'
      let chosen := Classical.choose (unique.exists)
      have h_chosen_spec := Classical.choose_spec (unique.exists)
      have h_eq_z := unique.unique h_chosen_spec ⟨r_in_R, hξ⟩
      apply Subtype.ext
      exact h_eq_z
    exact ⟨h', h_eq⟩
  exact ⟨g, by intro h'; rfl, h_surj⟩

/-! ## Auxiliary Lemma 3: Cardinality inequality using Finset.card_le_card_of_injOn -/

/-- If there is a surjective mapping g : {h // h ∈ D} → {r // r ∈ R},
    then D.card ≥ R.card. This follows by constructing an injection from R into D. -/
lemma card_ge_from_surj_on
    {D R : Finset Value}
    (g : {h // h ∈ D} → {r // r ∈ R})
    (h_surj : ∀ (r : Value) (r_in_R : r ∈ R), ∃ (h' : {h // h ∈ D}), g h' = ⟨r, r_in_R⟩) :
    D.card ≥ R.card :=
by
  -- Construct f : Value → Value that picks a preimage for each r in R.
  let f (r : Value) : Value :=
    if hr : r ∈ R then
      let h' := Classical.choose (h_surj r hr)
      h'.val
    else r
  -- Prove f is injective on R.
  have h_inj_on_R : ∀ r1 ∈ R, ∀ r2 ∈ R, f r1 = f r2 → r1 = r2 := by
    intro r1 hr1 r2 hr2 h_eq
    simp only [f, hr1, hr2] at h_eq
    have h_g1 := Classical.choose_spec (h_surj r1 hr1)
    have h_g2 := Classical.choose_spec (h_surj r2 hr2)
    have h_sub_eq : (Classical.choose (h_surj r1 hr1) : {x // x ∈ D}) =
                   (Classical.choose (h_surj r2 hr2) : {x // x ∈ D}) := by
      apply Subtype.ext
      exact h_eq
    rw [h_sub_eq] at h_g1
    rw [h_g2] at h_g1
    exact (Subtype.ext_iff.mp h_g1).symm
  -- f maps R into D.
  have h_f_image : ∀ r ∈ R, f r ∈ D := by
    intro r hr
    simp only [f, hr]
    exact (Classical.choose (h_surj r hr)).property
  -- Apply Finset.card_le_card_of_injOn.
  exact Finset.card_le_card_of_injOn (fun r => f r) h_f_image h_inj_on_R

/-! ## Auxiliary Lemma 4: Pigeonhole principle using Finset.card_le_card_of_injOn -/

/-- If g : {h // h ∈ D} → {r // r ∈ R} is surjective and |D| > |R|,
    then g is not injective: two distinct h values map to the same r. -/
lemma pigeonhole_surjective
    {D R : Finset Value}
    (g : {h // h ∈ D} → {r // r ∈ R})
    (h_card_gt : D.card > R.card) :
    ∃ (h1' h2' : {h // h ∈ D}), h1' ≠ h2' ∧ g h1' = g h2' :=
by
  by_contra h_neg
  let f (h : Value) : Value :=
    if hh : h ∈ D then
      let h' : {h // h ∈ D} := ⟨h, hh⟩
      (g h').val
    else h
  have h_inj_on_D : ∀ h1 ∈ D, ∀ h2 ∈ D, f h1 = f h2 → h1 = h2 := by
    intros h1 hh1 h2 hh2 h_eq
    simp only [f, hh1, hh2] at h_eq
    let h1' : {h // h ∈ D} := ⟨h1, hh1⟩
    let h2' : {h // h ∈ D} := ⟨h2, hh2⟩
    have h_g_eq : g h1' = g h2' := by apply Subtype.ext; exact h_eq
    by_contra h_ne_val
    have h_ne_sub : h1' ≠ h2' := fun heq => h_ne_val (congr_arg Subtype.val heq)
    have h_contr : ∃ (h1' h2' : {h // h ∈ D}), h1' ≠ h2' ∧ g h1' = g h2' :=
      ⟨h1', h2', h_ne_sub, h_g_eq⟩
    contradiction
  have h_f_image : ∀ h ∈ D, f h ∈ R := by
    intro h hh
    simp only [f, hh]
    exact (g ⟨h, hh⟩).property
  have h_card_le := Finset.card_le_card_of_injOn (fun h => f h) h_f_image h_inj_on_D
  exact (Nat.not_le.mpr h_card_gt) h_card_le

/-! ## Auxiliary Lemma 5: Obtain ξ from g -/

/-- If g maps two distinct hypothesis values to the same reference value,
    then both satisfy the ξ relation with that reference value. -/
lemma ξ_from_g
    (M Z : Model) (train : List Sample) (c : Component)
    {D R : Finset Value}
    (g : {h // h ∈ D} → {r // r ∈ R})
    (h1' h2' : {h // h ∈ D})
    (h_eq : g h1' = g h2')
    (h_exists_unique : ∀ h ∈ D, ∃! z ∈ R, ξ M Z train c h z)
    (h_g_def : ∀ h' : {h // h ∈ D},
        g h' = ⟨Classical.choose (h_exists_unique h'.val h'.property).exists,
               (Classical.choose_spec (h_exists_unique h'.val h'.property).exists).1⟩) :
    let h1 := h1'.val; let h2 := h2'.val
    let z := (g h1').val
    ξ M Z train c h1 z ∧ ξ M Z train c h2 z :=
by
  let h1 := h1'.val; let h2 := h2'.val
  let z := (g h1').val
  let unique1 := h_exists_unique h1 h1'.property
  let chosen1 := Classical.choose (unique1.exists)
  have h_spec1 := Classical.choose_spec (unique1.exists)
  let unique2 := h_exists_unique h2 h2'.property
  let chosen2 := Classical.choose (unique2.exists)
  have h_spec2 := Classical.choose_spec (unique2.exists)
  -- From h_g_def we directly get z = chosen1.
  have h_z_eq1 : z = chosen1 :=
    congr_arg Subtype.val (h_g_def h1')
  -- Using h_eq, replace g h1' with g h2', then get z = chosen2.
  have h_z_eq2 : z = chosen2 := by
    dsimp [z]
    rw [h_eq]
    exact congr_arg Subtype.val (h_g_def h2')
  -- Substitute to get the ξ relations.
  have hξ1 : ξ M Z train c h1 z := h_z_eq1 ▸ h_spec1.2
  have hξ2 : ξ M Z train c h2 z := h_z_eq2 ▸ h_spec2.2
  exact ⟨hξ1, hξ2⟩

/-! ### Auxiliary lemma: Sum of distribution after merging events is unchanged -/

/-- For finite set D and two distinct elements h1, h2 ∈ D, define q by merging
    h1 into h2 (adding probabilities) and setting h2 to 0.
    Then the total sum of q over D equals the total sum of p over D.
    Used in the entropy-decrease proof to show q is a valid distribution. -/
lemma sum_q_eq_sum_p
    (D : Finset Value) (h1 h2 : Value)
    (h1_in : h1 ∈ D) (h2_in : h2 ∈ D) (h_ne : h1 ≠ h2)
    (p : Value → ℝ) :
    let q := fun h => if h = h1 then p h1 + p h2
                      else if h = h2 then 0
                      else p h
    ∑ h ∈ D, q h = ∑ h ∈ D, p h :=
by
  intro q
  have hsum : ∑ h ∈ D, q h = q h1 + q h2 + ∑ h ∈ (D.erase h1).erase h2, q h := by
    calc
      ∑ h ∈ D, q h = q h1 + ∑ h ∈ D.erase h1, q h := by
        rw [← add_comm, ← Finset.sum_erase_add D q h1_in, add_comm]
      _ = q h1 + (q h2 + ∑ h ∈ (D.erase h1).erase h2, q h) := by
        rw [← add_comm (∑ h ∈ (D.erase h1).erase h2, q h),
          ← Finset.sum_erase_add (D.erase h1) q
            (mem_erase_of_ne_of_mem (Ne.symm h_ne) h2_in), add_comm]
      _ = q h1 + q h2 + ∑ h ∈ (D.erase h1).erase h2, q h := by ring
  rw [hsum]
  have hq1 : q h1 = p h1 + p h2 := by simp [q]
  have hq2 : q h2 = 0 := by simp [q, h_ne.symm]
  have hq_rest : ∀ h ∈ (D.erase h1).erase h2, q h = p h := by
    intro h hS
    rcases Finset.mem_erase.mp hS with ⟨hne2, hmem⟩
    rcases Finset.mem_erase.mp hmem with ⟨hne1, hmemD⟩
    simp [q, hne1, hne2]
  rw [hq1, hq2, add_zero]
  have hsum_replace : (∑ h ∈ (D.erase h1).erase h2, q h) = (∑ h ∈ (D.erase h1).erase h2, p h) :=
    Finset.sum_congr rfl (fun h hh => hq_rest h hh)
  rw [hsum_replace]
  calc
    p h1 + p h2 + ∑ h ∈ (D.erase h1).erase h2, p h
        = p h1 + (p h2 + ∑ h ∈ (D.erase h1).erase h2, p h) := by ring
    _ = p h1 + ∑ h ∈ D.erase h1, p h := by
        simpa [add_comm, add_left_comm, add_assoc] using congrArg (fun t => p h1 + t)
          (Finset.sum_erase_add (D.erase h1) p
            (mem_erase_of_ne_of_mem (Ne.symm h_ne) h2_in))
    _ = ∑ h ∈ D, p h := by
        simpa [add_comm] using Finset.sum_erase_add D p h1_in

end TACG.ExampleApproach.MinimumEntropyImpliesMinimizedRepresentationHelper
