import TACG.Definitions
import TACG.Derivations.Helper.SetMembership
import Mathlib.Data.Finset.Card

open TACG.Definitions
open TACG.Derivations.Helper.SetMembership

namespace TACG.Derivations.Necessity.ReferenceGraphSetConstruction

/-! ### Auxiliary definitions -/

/-- Relation R on domain `dom` and image `img` forms a bijection (functional,
    surjective, injective). Used to express that ξ is a bijection. -/
def BijectiveRelation (R : Value → Value → Prop) (dom img : Finset Value) : Prop :=
  (∀ x ∈ dom, ∃! y ∈ img, R x y) ∧
  (∀ y ∈ img, ∃! x ∈ dom, R x y)

/-! ### Auxiliary lemmas -/

/-- From correct training and compositional generalization, derive correct
    predictions on the entire dataset (train ∪ test). -/
private lemma correct_predictions_on_all (M : Model) (train test : List Sample)
    (h_correct_train : correct_predictions M train)
    (h_cg : CompositionalGeneralization M train test) :
    correct_predictions M (train ++ test) := by
  intro s hs
  rw [List.mem_append] at hs
  rcases hs with h | h
  · exact h_correct_train s h
  · exact h_cg h_correct_train s h

/-- Any model is structurally aligned with itself. -/
private lemma self_structural_alignment (M : Model) (samples : List Sample) :
    StructuralAlignment M M samples :=
  fun _ _ => ⟨rfl, ⟨rfl, ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩⟩⟩

/-- In the self-model, for any value in ξ_set, ξ relates it to itself. -/
private lemma self_ξ_exists (M : Model) (train : List Sample) (c : Component) (h : Value)
    (h_in_dom : h ∈ ξ_set M train c) :
    ξ M M train c h h := by
  rcases ξ_set_mem_elim M train c h h_in_dom with ⟨A, hA, out, h_out, h_comp, h_eq⟩
  exact ⟨A, hA, out, h_out, h_comp, h_eq, h_eq⟩

/-- In the self-model, ξ relates h to z only if h = z. -/
lemma self_ξ_eq (M : Model) (train : List Sample) (c : Component) (h z : Value) :
    ξ M M train c h z → h = z := by
  rintro ⟨_, _, _, _, _, h_eq, z_eq⟩
  exact h_eq.symm.trans z_eq

/-- For the self-model, ξ is a bijection between ξ_set and itself. -/
private lemma self_ξ_bijective (M : Model) (train : List Sample) (c : Component) :
    BijectiveRelation (ξ M M train c) (ξ_set M train c) (ξ_set M train c) := by
  let dom := ξ_set M train c
  constructor
  · intro h h_in_dom
    have h_self := self_ξ_exists M train c h h_in_dom
    exact ⟨h, ⟨h_in_dom, h_self⟩, fun z ⟨_, rel⟩ => (self_ξ_eq M train c h z rel).symm⟩
  · intro z z_in_dom
    have z_self := self_ξ_exists M train c z z_in_dom
    exact ⟨z, ⟨z_in_dom, z_self⟩, fun h ⟨_, rel⟩ => self_ξ_eq M train c h z rel⟩

/-! ### Main lemma -/

/-- Lemma 5: Reference Graph Set Construction.
    Under correct training, compositional generalization, and seen test inputs,
    the model itself can serve as a reference model, satisfying structural
    alignment and bijective self-ξ mappings. -/
lemma reference_graph_set_construction (M : Model) (train test : List Sample)
    (h_correct_train : correct_predictions M train)
    (h_cg : CompositionalGeneralization M train test)
    (h_seen : seen_inputs_condition M train test) :
    ∃ Z : ReferenceModel train test,
      Z.model = M ∧
      StructuralAlignment M M (train ++ test) ∧
      ∀ c ∈ components_list M train,
        BijectiveRelation (ξ M M train c) (ξ_set M train c) (ξ_set M train c) := by
  have h_correct_all := correct_predictions_on_all M train test h_correct_train h_cg
  let Z : ReferenceModel train test := {
    model := M,
    correctness := h_correct_all,
    seen_inputs := h_seen
  }
  have struc_align := self_structural_alignment M (train ++ test)
  have bijective_property : ∀ c ∈ components_list M train,
      BijectiveRelation (ξ M M train c) (ξ_set M train c) (ξ_set M train c) :=
    fun c _ => self_ξ_bijective M train c
  exact ⟨Z, rfl, struc_align, bijective_property⟩

end TACG.Derivations.Necessity.ReferenceGraphSetConstruction
