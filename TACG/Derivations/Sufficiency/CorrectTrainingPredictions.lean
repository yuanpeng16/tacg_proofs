import TACG.Definitions

open TACG.Definitions

/-- Lemma 9 (Correct Training Predictions).
    This is a direct application of the definition of `correct_predictions`:
    if a model is correct on all training samples, then for any particular
    training sample A, the output nodes of its graph equal the sample's output.
    This lemma is used in the sufficiency proof as a premise. -/
lemma correct_training_prediction {M : Model} {train : List Sample}
    (h_correct : correct_predictions M train)
    (A : Sample) (hA : A ∈ train) :
    let g := M.graphSet A
    g.output_nodes.map g.node_value = g.output_nodes.map A.output :=
  h_correct A hA
