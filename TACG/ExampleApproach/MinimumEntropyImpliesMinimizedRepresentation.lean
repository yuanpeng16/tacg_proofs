import TACG.Definitions
import TACG.ExampleApproach.EntropyDecreasesUnderEventMerging
import TACG.ExampleApproach.MinimumEntropyImpliesMinimizedRepresentationHelper

open TACG.Definitions
open TACG.ExampleApproach.EntropyDecreasesUnderEventMerging
open TACG.ExampleApproach.MinimumEntropyImpliesMinimizedRepresentationHelper

namespace TACG.ExampleApproach.MinimumEntropyImpliesMinimizedRepresentation

/-! ## Main theorem -/

/-- A distribution p on a finite set D has minimal entropy if every other
    valid distribution q on D has entropy at least that of p. -/
def IsMinimalEntropy (D : Finset Value) (p : Value → ℝ) : Prop :=
  ∀ q : Value → ℝ,
    (∀ h ∈ D, q h ≥ 0) →
    Finset.sum D (fun h => q h) = 1 →
    entropy D p ≤ entropy D q

/-- Lemma 3 from the paper: Minimum entropy implies minimized representation.
    If a component c has minimum entropy over its hypothesis values (on D),
    then its domain size equals the reference image size, i.e., minimized
    representation (Definition 9) holds.

    The proof proceeds as follows:
    1. Unambiguous representation ensures that each hypothesis value maps to a
       unique reference value. When constructing a new distribution, the only
       allowed operation is to merge distinct hypothesis values that already
       share the same reference value; splitting is not permitted.
    2. Assume for contradiction that the representation is not minimized.
       Then |D| > |R|. By surjectivity of the mapping g : D → R and the
       pigeonhole principle, two distinct hypothesis values h1, h2 ∈ D map to
       the same reference value.
    3. Merge h1 and h2 in the probability distribution p to obtain q.
    4. By Lemma 15 (entropy decreases under event merging), entropy(q) < entropy(p),
       contradicting the minimality of p.
-/
lemma minimum_entropy_implies_minimized_representation
    (M Z : Model) (train : List Sample) (c : Component)
    (h_struct : StructuralAlignment M Z train)
    (h_unambig : UnambiguousRepresentation c train M Z)
    (p : Value → ℝ)
    (h_support : ∀ h, h ∈ ξ_set M train c ↔ p h > 0)
    (h_sum : Finset.sum (ξ_set M train c) (fun h => p h) = 1)
    (h_min_entropy : IsMinimalEntropy (ξ_set M train c) p)
    : MinimizedRepresentation c train M Z :=
by
  by_contra h_not_min
  let D := ξ_set M train c
  let R := ξ_set Z train c
  -- 1. From unambiguous representation, each h in D maps to a unique z in R.
  have h_exists_unique : ∀ h ∈ D, ∃! z, z ∈ R ∧ ξ M Z train c h z :=
    fun h h_in_D => exists_unique_mapping M Z train c h_struct h_unambig h h_in_D
  -- 2. Construct a surjective mapping g from D to R via the unique z for each h.
  obtain ⟨g, h_g_def, h_surj⟩ :=
    surjective_g M Z train c h_struct D R rfl rfl h_exists_unique
  -- 3. Surjectivity gives |D| >= |R|. Since representation is not minimized,
  --    we must have strict inequality |D| > |R|.
  have h_card_ge := card_ge_from_surj_on g h_surj
  have h_card_gt : D.card > R.card :=
    lt_of_le_of_ne h_card_ge (fun h_eq => h_not_min (Eq.symm h_eq))
  -- 4. By the pigeonhole principle, two distinct h values map to the same z.
  obtain ⟨h1', h2', h_ne, h_eq_g⟩ := pigeonhole_surjective g h_card_gt
  let h1_val := h1'.val; let h2_val := h2'.val
  have h1_in_D : h1_val ∈ D := h1'.property
  have h2_in_D : h2_val ∈ D := h2'.property
  have h_ne' : h1_val ≠ h2_val := by intro eq; apply h_ne; apply Subtype.ext eq
  -- 5. From g we obtain the corresponding ξ relations.
  have ⟨hξ1, hξ2⟩ := ξ_from_g M Z train c g h1' h2' h_eq_g h_exists_unique h_g_def
  -- 6. Merge the two distinct hypothesis values h1_val and h2_val in distribution p.
  have h_pos1 : p h1_val > 0 := (h_support h1_val).mp h1_in_D
  have h_pos2 : p h2_val > 0 := (h_support h2_val).mp h2_in_D
  let q : Value → ℝ := fun h =>
    if h = h1_val then p h1_val + p h2_val
    else if h = h2_val then 0
    else p h
  -- q is a valid probability distribution on D (nonnegative and sums to 1).
  have h_q_nonneg : ∀ h ∈ D, q h ≥ 0 := by
    intros h hD
    dsimp [q]
    split_ifs
    · exact add_nonneg (le_of_lt h_pos1) (le_of_lt h_pos2)
    · exact le_rfl   -- 0 ≤ 0
    · exact le_of_lt ((h_support h).mp hD)
  -- The sum of q equals the sum of p, which is 1.
  have h_q_sum : ∑ h ∈ D, q h = 1 :=
    calc
      ∑ h ∈ D, q h = ∑ h ∈ D, p h := sum_q_eq_sum_p D h1_val h2_val h1_in_D h2_in_D h_ne' p
      _ = 1 := h_sum
  -- 7. Merging two events strictly decreases entropy (Lemma 15).
  have h_ent_decrease :=
    entropy_decreases_under_event_merging D h1_val h2_val h1_in_D h2_in_D h_ne' p
      (fun i hi => le_of_lt ((h_support i).mp hi)) h_sum h_pos1 h_pos2
  -- 8. Minimal entropy of p implies entropy(p) <= entropy(q), contradicting strict decrease.
  have h_ent_min := h_min_entropy q h_q_nonneg h_q_sum
  exact not_lt.mpr h_ent_min h_ent_decrease

end TACG.ExampleApproach.MinimumEntropyImpliesMinimizedRepresentation
