import TACG.Definitions
import TACG.Derivations.Helper.SetMembership

open TACG.Definitions
open TACG.Derivations.Helper.SetMembership

namespace TACG.Derivations.Necessity.NecessityDirection

/-- The hypothesis model itself is structurally aligned with itself. -/
private lemma self_structural_alignment (M : Model) (samples : List Sample) :
    StructuralAlignment M M samples :=
  fun _ _ => ⟨rfl, ⟨rfl, ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩⟩⟩

/-- In the self-model, ξ relates h to z only if h = z. -/
private lemma self_ξ_eq (M : Model) (train : List Sample) (c : Component) (h z : Value) :
    ξ M M train c h z → h = z := by
  rintro ⟨_, _, _, _, _, h_eq, z_eq⟩
  exact h_eq.symm.trans z_eq

/-- For the self-model, ξ_set for M and M are identical, so minimized holds trivially. -/
private lemma self_minimized (M : Model) (train : List Sample) (c : Component) :
    MinimizedRepresentation c train M M := by
  unfold MinimizedRepresentation
  rfl

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

/-- Proposition 1 (Necessity): if a model provably enables compositional generalization,
    then it satisfies AS-UMR. This lemma constructs the reference model from the
    hypothesis model itself and verifies the three conditions.

    Proof structure:
    1. By correct training and compositional generalization, all predictions are correct.
    2. By the seen-inputs assumption, all test component inputs appear in training.
       Hence the hypothesis model itself satisfies the reference model conditions.
    3. Taking Z = M yields structural alignment trivially.
    4. Unambiguous representation holds because in the self-model, each hypothesis value
       maps to exactly one reference value (itself).
    5. Minimized representation holds because the hypothesis and reference value sets
       are identical, hence have equal cardinalities. -/
lemma necessity_direction (M : Model) (train test : List Sample)
    (h_cg : CompositionalGeneralization M train test)
    (h_correct_train : correct_predictions M train)
    (h_seen : seen_inputs_condition M train test) :
    AS_UMR M train test := by
  -- Step 1: correctness on all samples
  have h_correct_all := correct_predictions_on_all M train test h_correct_train h_cg
  -- Step 2: construct the reference model Z = M
  let Z : ReferenceModel train test := {
    model := M,
    correctness := h_correct_all,
    seen_inputs := h_seen
  }
  -- Step 3: structural alignment is trivial for Z = M
  have h_struc : StructuralAlignment M Z.model (train ++ test) :=
    self_structural_alignment M (train ++ test)
  -- Step 4: for every component used in training, both unambiguous and minimized
  have unamb_min : ∀ c ∈ components_list M train,
      UnambiguousRepresentation c train M Z.model ∧
      MinimizedRepresentation c train M Z.model := by
    intro c hc
    -- Unambiguous: Z = M, so ξ(h,z) implies h = z
    have unamb : UnambiguousRepresentation c train M Z.model := by
      unfold UnambiguousRepresentation
      intros h_val _ z1 z2 rel1 rel2
      have eq1 := self_ξ_eq M train c h_val z1 rel1
      have eq2 := self_ξ_eq M train c h_val z2 rel2
      exact eq1.symm.trans eq2
    -- Minimized: ξ_set are identical
    have minimized : MinimizedRepresentation c train M Z.model :=
      self_minimized M train c
    exact ⟨unamb, minimized⟩
  -- Step 5: conclude AS-UMR
  exact ⟨Z, h_struc, unamb_min⟩

end TACG.Derivations.Necessity.NecessityDirection
