/-
Formalization of definitions from the paper:
"A Theoretical Analysis of Provable Compositional Generalization in Neural Networks:
A Necessary and Sufficient Condition".

This file defines the core notions: Node, Value, Sample, Component, Graph,
Model, reference models, structural alignment, unambiguous/minimized
representations, AS‑UMR, and the main theorem conditions.
-/

import Mathlib.Data.Finset.Card

namespace TACG.Definitions

/- Abstract types for nodes and values -/
opaque Node : Type
opaque Value : Type

noncomputable instance : DecidableEq Node := Classical.decEq Node
noncomputable instance : DecidableEq Value := Classical.decEq Value

/-- Definition of a sample: a pair of input and output mappings (Definition in Section 2.1). -/
structure Sample where
  input : Node → Value
  output : Node → Value

/-- Component identifier: arity and whether it produces graph output nodes.
    Corresponds to Definition 1 (Component). -/
structure Component where
  arity : ℕ
  is_graph_output : Bool   -- nodes from this component must be output nodes

noncomputable instance : DecidableEq Component := Classical.decEq Component

/-- Special input component (not a graph output), used for input nodes. -/
def inputComponent : Component :=
  { arity := 0, is_graph_output := false }

/-- A computational graph (without apply_of, supplied by Model).
    Definition 2 (Computational Graph) in the paper.
    Every non‑input node has a component and a list of input nodes,
    satisfying topological order and arity matching.
    Conditions: no dangling nodes, no duplicates in ordered node list,
    output nodes are not used as inputs, output‑component consistency. -/
structure Graph where
  input_nodes : List Node
  intermediate_nodes : List Node
  output_nodes : List Node
  node_value : Node → Value
  node_component : Node → Component
  node_inputs : Node → List Node

  -- All nodes in input_nodes ++ intermediate_nodes ++ output_nodes are distinct
  ordered_nodup : List.Nodup (input_nodes ++ intermediate_nodes ++ output_nodes)

  -- Every input node of any node belongs to the graph's node universe
  input_nodes_in_graph :
    ∀ (n : Node), ∀ (m : Node), m ∈ node_inputs n →
      m ∈ input_nodes ++ intermediate_nodes ++ output_nodes

  -- Output nodes never appear as inputs to any non‑input node
  output_not_used : ∀ (n : Node), n ∈ output_nodes →
    ∀ (m : Node), m ∈ intermediate_nodes ++ output_nodes → n ∉ node_inputs m

  -- Input nodes use the special inputComponent
  node_component_input : ∀ (n : Node), n ∈ input_nodes → node_component n = inputComponent

  -- Non‑input nodes cannot use inputComponent
  non_input_component_not_input :
    ∀ (n : Node), n ∈ intermediate_nodes ++ output_nodes → node_component n ≠ inputComponent

  -- A non‑input node is an output node iff its component says so
  output_component_consistency : ∀ (n : Node), n ∈ intermediate_nodes ++ output_nodes →
    (n ∈ output_nodes ↔ (node_component n).is_graph_output)

  -- No dangling nodes: every input or intermediate node is used as input by some non‑input node
  no_dangling_nodes : ∀ (n : Node),
    n ∈ input_nodes ++ intermediate_nodes →
    ∃ (m : Node), m ∈ intermediate_nodes ++ output_nodes ∧ n ∈ node_inputs m

  -- Arity of each non‑input node matches its component arity
  arity_match :
    ∀ (n : Node), n ∈ intermediate_nodes ++ output_nodes →
      (node_inputs n).length = (node_component n).arity

  -- Topological order: every input of a non‑input node appears earlier in the ordered list
  topological_order : ∀ (n : Node),
    n ∈ intermediate_nodes ++ output_nodes → ∀ (m : Node), m ∈ node_inputs n →
    let ordered := input_nodes ++ intermediate_nodes ++ output_nodes
    ordered.findIdx (· == m) < ordered.findIdx (· == n)

/-- Helper: all non‑input nodes (intermediate + output) of a graph.
    Used to simplify statements about non-input nodes. -/
def Graph.non_input_nodes (g : Graph) : List Node :=
  g.intermediate_nodes ++ g.output_nodes

/-- A Model provides a global apply_of function and a graph for each sample.
    It also ensures that input node values match the sample's input.
    This corresponds to the hypothesis graph set H in the paper. -/
structure Model where
  apply_of : Component → List Value → Value
  graphSet : Sample → Graph

  -- Every non‑input node's value is computed by apply_of using its component and input values
  comp_valuation : ∀ (s : Sample), ∀ (n : Node), n ∈ (graphSet s).non_input_nodes →
    let g := graphSet s
    let comp := g.node_component n
    let ins := g.node_inputs n
    g.node_value n = apply_of comp (ins.map g.node_value)

  -- Input nodes take their values from the sample input
  input_nodes_correct : ∀ (s : Sample) (n : Node), n ∈ (graphSet s).input_nodes →
    (graphSet s).node_value n = s.input n

/-- Correct predictions: output node values match the sample output.
    Used in Definition 4 (Reference Graph Set) and Definition 5. -/
def correct_predictions (M : Model) (dataset : List Sample) : Prop :=
  ∀ (s : Sample), s ∈ dataset →
    let g := M.graphSet s
    g.output_nodes.map g.node_value = g.output_nodes.map s.output

/-- Collect all non‑output components (i.e., components of intermediate nodes)
    used by the model on the given samples, deduplicated.
    This is the set C in the paper (non-output component set). -/
noncomputable def components_list (M : Model) (samples : List Sample) : List Component :=
  (samples.map (fun s =>
    (M.graphSet s).intermediate_nodes.map (M.graphSet s).node_component)).flatten
  |> List.dedup

/-- Condition that every test component input has been seen in training.
    For each non‑input node of a test sample, there exists a training sample
    with a node of the same component and equal input values and component sequence.
    This is part of Definition 4 (Reference Graph Set) and Assumption 1. -/
def seen_inputs_condition (M : Model) (train test : List Sample) : Prop :=
  ∀ (B : Sample), B ∈ test →
    let gB := M.graphSet B
    ∀ (outB : Node), outB ∈ gB.non_input_nodes →
      let compB := gB.node_component outB
      let insB := gB.node_inputs outB
      ∃ (A : Sample), A ∈ train ∧
        let gA := M.graphSet A
        ∃ (outA : Node), outA ∈ gA.non_input_nodes ∧
          gA.node_component outA = compB ∧
          (gA.node_inputs outA).map gA.node_value = insB.map gB.node_value ∧
          (gA.node_inputs outA).map gA.node_component = insB.map gB.node_component

/-- Reference model: correct on all samples and all test component inputs seen.
    This formalizes Definition 4 (Reference Graph Set) with explicit model structure. -/
structure ReferenceModel (train test : List Sample) where
  model : Model
  correctness : correct_predictions model (train ++ test)
  seen_inputs : seen_inputs_condition model train test

/-- Compositional generalization (Definition 5 in the paper).
    If training predictions are correct, then test predictions are also correct. -/
def CompositionalGeneralization (M : Model) (train test : List Sample) : Prop :=
  correct_predictions M train → correct_predictions M test

/-- Structural alignment (Definition 6 in the paper).
    For each sample, the two graphs are identical in node lists, component
    assignments, and input edges. Denoted H ≅_S Z. -/
def StructuralAlignment (M1 M2 : Model) (samples : List Sample) : Prop :=
  ∀ (s : Sample), s ∈ samples →
    let g1 := M1.graphSet s
    let g2 := M2.graphSet s
    g1.input_nodes = g2.input_nodes ∧
    g1.intermediate_nodes = g2.intermediate_nodes ∧
    g1.output_nodes = g2.output_nodes ∧
    ∀ (n : Node), n ∈ g1.non_input_nodes →
      g1.node_component n = g2.node_component n ∧
      g1.node_inputs n = g2.node_inputs n

/-- Value mapping ξ (Definition 7 in the paper).
    Relates hypothesis value to reference value for a component c,
    using intermediate nodes only (non‑output components). -/
def ξ (M1 M2 : Model) (train : List Sample) (c : Component) : Value → Value → Prop :=
  fun h_val z_val =>
    ∃ (A : Sample), A ∈ train ∧
      ∃ (out : Node),
        out ∈ (M1.graphSet A).intermediate_nodes ∧
        (M1.graphSet A).node_component out = c ∧
        (M1.graphSet A).node_value out = h_val ∧
        (M2.graphSet A).node_value out = z_val

/-- Set of all hypothesis (or reference) values for component c on training data,
    collected from intermediate nodes only.
    Used in Definitions 8, 9, and 10. -/
noncomputable def ξ_set (M : Model) (train : List Sample) (c : Component) : Finset Value :=
  List.toFinset (List.flatten (train.map (fun A =>
    let g := M.graphSet A
    List.map (fun out => g.node_value out)
      (List.filter (fun out => g.node_component out = c) g.intermediate_nodes))))

/-- Unambiguous representation (Definition 8 in the paper).
    Each hypothesis value maps to at most one reference value. -/
def UnambiguousRepresentation (c : Component) (train : List Sample) (M1 M2 : Model) : Prop :=
  ∀ (h_val : Value) (_ : h_val ∈ ξ_set M1 train c) (z1 z2 : Value),
    ξ M1 M2 train c h_val z1 → ξ M1 M2 train c h_val z2 → z1 = z2

/-- Minimized representation (Definition 9 in the paper).
    The number of distinct hypothesis values equals the number of distinct
    reference values (no redundancy). -/
def MinimizedRepresentation (c : Component) (train : List Sample) (M1 M2 : Model) : Prop :=
  (ξ_set M1 train c).card = (ξ_set M2 train c).card

/-- AS‑UMR (Definition 10 in the paper):
    Aligned Structure‑Unambiguous Minimized Representation.
    Existence of a reference model satisfying structural alignment, and for
    every used non‑output component, both unambiguous and minimized representations. -/
def AS_UMR (M : Model) (train test : List Sample) : Prop :=
  let used_comps := components_list M train
  ∃ (Z : ReferenceModel train test),
    StructuralAlignment M Z.model (train ++ test) ∧
    ∀ (c : Component), c ∈ used_comps →
      UnambiguousRepresentation c train M Z.model ∧
      MinimizedRepresentation c train M Z.model

/-- Alternative compositional generalization (Definition 14 in the paper):
    original definition plus the seen‑inputs condition. -/
def AlternativeCompositionalGeneralization (M : Model) (train test : List Sample) : Prop :=
  CompositionalGeneralization M train test ∧ seen_inputs_condition M train test

/-- Injective representation (Definition 15 in the paper).
    Each reference value has at most one hypothesis value. -/
def InjectiveRepresentation (c : Component) (train : List Sample) (M1 M2 : Model) : Prop :=
  ∀ (z : Value) (_ : z ∈ ξ_set M2 train c) (h1 h2 : Value),
    ξ M1 M2 train c h1 z → ξ M1 M2 train c h2 z → h1 = h2

/-- AS‑IR (Definition 16 in the paper):
    Aligned Structure‑Injective Representation. -/
def AS_IR (M : Model) (train test : List Sample) : Prop :=
  let used_comps := components_list M train
  ∃ (Z : ReferenceModel train test),
    StructuralAlignment M Z.model (train ++ test) ∧
    ∀ (c : Component), c ∈ used_comps →
      InjectiveRepresentation c train M Z.model

end TACG.Definitions
