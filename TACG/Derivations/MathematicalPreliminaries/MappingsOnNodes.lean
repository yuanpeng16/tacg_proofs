import Mathlib.Logic.Function.Basic
import TACG.Derivations.MathematicalPreliminaries.EqualSetSize

open Function
open TACG.Derivations.MathematicalPreliminaries.EqualSetSize

namespace TACG.Derivations.MathematicalPreliminaries.MappingsOnNodes

/-- Lemma 1 (Mappings on Nodes) from the paper.
    For finite sets S₁ (hypothesis representations) and S₂ (reference representations),
    given a well-defined and surjective mapping f : S₁ → S₂,
    f is injective iff |S₁| = |S₂|, i.e., the domain size is minimized.
    This equivalence is a direct instantiation of `equal_set_size`.
    It is used to show that minimized representation plus unambiguous representation
    implies injective representation, which is crucial for the induction step. -/
lemma mappings_on_nodes {S₁ S₂ : Type} [Fintype S₁] [Fintype S₂] (f : S₁ → S₂)
(hf_surj : Surjective f) :
    Injective f ↔ Fintype.card S₁ = Fintype.card S₂ :=
  equal_set_size f hf_surj

end TACG.Derivations.MathematicalPreliminaries.MappingsOnNodes
