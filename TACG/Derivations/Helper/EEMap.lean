import Mathlib.Data.List.Basic

namespace TACG.Derivations.Helper.EEMap

/-- If two mapped lists are equal, then elementwise the function values are equal
    at the same index, provided both indices are within bounds. -/
lemma get_eq_of_eq_map {α β γ : Type} (f1 : α → β) (f2 : γ → β) {l1 : List α} {l2 : List γ}
    (h : l1.map f1 = l2.map f2) (i : ℕ) (hi1 : i < l1.length) (hi2 : i < l2.length) :
    f1 (l1.get ⟨i, hi1⟩) = f2 (l2.get ⟨i, hi2⟩) := by
  calc
    f1 (l1.get ⟨i, hi1⟩) = (l1.map f1).get ⟨i, by simpa [List.length_map] using hi1⟩ := by simp
    _ = (l2.map f2).get ⟨i, by simpa [List.length_map] using hi2⟩ := by simp [h]
    _ = f2 (l2.get ⟨i, hi2⟩) := by simp

end TACG.Derivations.Helper.EEMap
