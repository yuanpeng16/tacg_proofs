import TACG.Definitions

open TACG.Definitions

/- Lemma 9 (Deterministic Components) from the paper:
   For a given model M, each component c is deterministic:
   if the input value lists are equal, then the output values are equal.
   This follows directly from the fact that `apply_of c` is a function
   (Definition of Component), ensuring that the same inputs always yield
   the same output. Used in the sufficiency proof for the induction step. -/
lemma deterministic_component (M : Model) (c : Component) (vs1 vs2 : List Value) (h : vs1 = vs2) :
    M.apply_of c vs1 = M.apply_of c vs2 := by
  rw [h]
