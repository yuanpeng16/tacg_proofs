import TACG.Definitions

open TACG.Definitions
open List

namespace TACG.Derivations.Sufficiency.IndexTopology

/-- If a list is nodup and the element at index i equals a, then the findIdx
    of a in the list is exactly i. Used to relate findIdx comparisons to actual
    list indices when the list is nodup (guaranteed by Graph.ordered_nodup). -/
private lemma findIdx_eq_of_get_eq_nodup {l : List Node} (hnd : l.Nodup) {a : Node}
  {i : ℕ} (hi : i < l.length) (hget : l.get ⟨i, hi⟩ = a) : findIdx (· == a) l = i := by
  induction l generalizing i with
  | nil => exact absurd hi (by simp)
  | cons x xs ih =>
    cases i with
    | zero =>
      have hx_eq_a : x = a := by simpa using hget
      simp [List.findIdx_cons, hx_eq_a]
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      have hget' : xs.get ⟨i, hi'⟩ = a := by simpa using hget
      have hx_ne_a : x ≠ a := by
        intro h_eq
        have hx_mem_xs : x ∈ xs := by
          rw [List.mem_iff_get]
          exact ⟨⟨i, hi'⟩, by rw [h_eq, hget']⟩
        exact (nodup_cons.mp hnd).left hx_mem_xs
      rw [List.findIdx_cons]
      by_cases hxeq : x == a
      · -- From hxeq we get x = a, contradicting hx_ne_a.
        exact absurd (eq_of_beq hxeq) hx_ne_a
      · -- hxeq is false, simplify bif.
        simp [hxeq, ih hnd.tail hi' hget']

/-- From a topological order's findIdx comparison derive the actual index
    order. Requires the ordered list to be nodup (guaranteed by
    Graph.ordered_nodup). This is used to apply topological_order in proofs
    that need index comparisons. -/
lemma index_lt_from_topological_order
    {ordered : List Node}
    (h_nodup : List.Nodup ordered)
    (m n : Node)
    (h_findIdx_lt : findIdx (· == m) ordered < findIdx (· == n) ordered)
    (j : ℕ) (hj : j < ordered.length) (hj_eq : ordered.get ⟨j, hj⟩ = m)
    (i : ℕ) (hi : i < ordered.length) (hi_eq : ordered.get ⟨i, hi⟩ = n) :
    j < i := by
  have hm := findIdx_eq_of_get_eq_nodup h_nodup hj hj_eq
  have hn := findIdx_eq_of_get_eq_nodup h_nodup hi hi_eq
  simpa [hm, hn] using h_findIdx_lt

end TACG.Derivations.Sufficiency.IndexTopology
