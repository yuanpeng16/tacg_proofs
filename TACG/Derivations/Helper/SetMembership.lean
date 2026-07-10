import TACG.Definitions
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

open TACG.Definitions

/-!
# Auxiliary lemmas: set membership conversion

This file provides helper lemmas about membership in `ξ_set` (the finite set of
component output values), converting between `Finset` representation and the
underlying list representation for structural decomposition and reasoning.
-/

namespace TACG.Derivations.Helper.SetMembership

/--
`mem_toFinset` establishes the equivalence between `List.toFinset` and
`List.dedup` with respect to membership.

For any type `α` with decidable equality and list `l`, an element `x` belongs to
`List.toFinset l` (as an element of `Finset`) iff `x` belongs to `l.dedup` (as
an element of the list).

This lemma is mainly used to convert membership in `ξ_set` (which returns a
`Finset`) into operations on the underlying list, enabling decomposition using
`List.mem_dedup`, `List.mem_flatten`, and `List.mem_map`.

Proof: `Finset.mem_def` rewrites `x ∈ s` to `s x` (`Finset` as predicate), and
`List.toFinset` is internally equivalent to a `Finset` built from `l.dedup`,
so both sides are definitionally equivalent; `rfl` closes the goal.
-/
lemma mem_toFinset {α : Type} [DecidableEq α] (x : α) (l : List α) :
    x ∈ List.toFinset l ↔ x ∈ l.dedup := by
  rw [Finset.mem_def]; rfl

/--
`ξ_set_mem_elim` is the backward elimination lemma for membership in `ξ_set`.

Given a model `Z`, training samples `train`, component `c`, and a value `z_val`,
if `z_val ∈ ξ_set Z train c` (i.e., some output value of component `c` on
training samples), then there exists a training sample `A` and an intermediate
node `out` such that:
- `out` is in the intermediate nodes of `Z.graphSet A`,
- `(Z.graphSet A).node_component out = c`,
- and `(Z.graphSet A).node_value out = z_val`.

This lemma reduces set membership to the existence of a corresponding node in
the concrete graph structure, and is a key step in proving `surjective_mapping`.

Proof sketch:
1. Unfold `ξ_set` to obtain `z_val ∈ List.toFinset (flatten ...)`.
2. Use `mem_toFinset` to convert to `z_val ∈ (flatten ...).dedup`.
3. Use `List.mem_dedup` to get `z_val ∈ flatten ...`.
4. Use `List.mem_flatten` to extract the sublist `L'` and its source sample `A`.
5. Further decompose `List.mem_map` to obtain the concrete output node `out`
   and its membership.
6. Use `List.mem_filter` to get `out ∈ gA.intermediate_nodes` and
   `gA.node_component out = c`.
7. Assemble the results to obtain the desired existential conclusion.
-/
lemma ξ_set_mem_elim (Z : Model) (train : List Sample) (c : Component) (z_val : Value) :
    z_val ∈ ξ_set Z train c →
    ∃ A ∈ train, ∃ out,
      out ∈ (Z.graphSet A).intermediate_nodes ∧
      (Z.graphSet A).node_component out = c ∧
      (Z.graphSet A).node_value out = z_val := by
  unfold ξ_set
  intro h
  rw [mem_toFinset] at h
  rw [List.mem_dedup] at h
  rw [List.mem_flatten] at h
  rcases h with ⟨L', hL', hz⟩
  rcases List.mem_map.mp hL' with ⟨A, hA, rfl⟩
  rw [List.mem_map] at hz
  rcases hz with ⟨out, h_out_mem, h_eq⟩
  rw [List.mem_filter] at h_out_mem
  rcases h_out_mem with ⟨h_out_in, h_comp_eq⟩
  have h_comp_eq' : (Z.graphSet A).node_component out = c := of_decide_eq_true h_comp_eq
  exact ⟨A, hA, out, h_out_in, h_comp_eq', h_eq⟩

end TACG.Derivations.Helper.SetMembership
