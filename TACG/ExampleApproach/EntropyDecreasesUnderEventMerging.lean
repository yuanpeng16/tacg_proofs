import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace TACG.ExampleApproach.EntropyDecreasesUnderEventMerging

/-- Core inequality: for x, y > 0, the entropy of a binary distribution is positive,
    equivalently x log x + y log y < (x + y) log(x + y).
    This is the key analytic fact used to show merging events reduces entropy. -/
private lemma mul_log_add_mul_log_lt_mul_log_add {x y : ℝ} (hx : x > 0) (hy : y > 0) :
    x * Real.log x + y * Real.log y < (x + y) * Real.log (x + y) := by
  have hsum_pos : x + y > 0 := add_pos hx hy
  have h1 : (x + y) / x > 1 := by
    have hdivpos : y / x > 0 := div_pos hy hx
    have h_eq : (x + y) / x = 1 + y / x := by
      field_simp [hx.ne']
      try ring
    rw [h_eq]
    linarith
  have h2 : (x + y) / y > 1 := by
    have hdivpos : x / y > 0 := div_pos hx hy
    have h_eq : (x + y) / y = 1 + x / y := by
      field_simp [hy.ne']
      try ring
    rw [h_eq]
    linarith
  have hlog1 : Real.log ((x + y) / x) > 0 := Real.log_pos h1
  have hlog2 : Real.log ((x + y) / y) > 0 := Real.log_pos h2
  have hpos1 : x * Real.log ((x + y) / x) > 0 := mul_pos hx hlog1
  have hpos2 : y * Real.log ((x + y) / y) > 0 := mul_pos hy hlog2
  have hsum : x * Real.log ((x + y) / x) + y * Real.log ((x + y) / y) > 0 := add_pos hpos1 hpos2
  have eq : (x + y) * Real.log (x + y) - (x * Real.log x + y * Real.log y) =
      x * Real.log ((x + y) / x) + y * Real.log ((x + y) / y) := by
    calc
      (x + y) * Real.log (x + y) - (x * Real.log x + y * Real.log y) =
          x * Real.log (x + y) + y * Real.log (x + y) - x * Real.log x - y * Real.log y := by ring
      _ = x * (Real.log (x + y) - Real.log x) + y * (Real.log (x + y) - Real.log y) := by ring
      _ = x * Real.log ((x + y) / x) + y * Real.log ((x + y) / y) := by
        rw [Real.log_div (hsum_pos.ne') hx.ne', Real.log_div (hsum_pos.ne') hy.ne']
  linarith

/-- Entropy of a finite probability distribution on a Finset.
    Defined as the negative sum of p(i) log p(i) over the support s. -/
noncomputable def entropy {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → ℝ) : ℝ :=
  -Finset.sum s (fun i => p i * Real.log (p i))

/-- Lemma 10 from the paper: Entropy strictly decreases when we merge two events
    with positive probability. Merging is realized by moving the probability of
    b onto a and setting b to zero. This is the key lemma for proving that
    minimum entropy implies minimized representation, since any redundant
    representation would allow merging two distinct values, strictly reducing
    entropy and contradicting minimality. -/
lemma entropy_decreases_under_event_merging {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι)
    (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) (p : ι → ℝ)
    (h_nonneg : ∀ i ∈ s, p i ≥ 0) (h_sum : Finset.sum s p = 1)
    (ha_pos : p a > 0) (hb_pos : p b > 0) :
    let q : ι → ℝ := fun i =>
      if i = a then p a + p b
      else if i = b then 0
      else p i
    entropy s q < entropy s p := by
  intro q
  have _ := h_nonneg
  have _ := h_sum
  -- Simplifications for q at a and b.
  have hq_a : q a = p a + p b := by
    dsimp [q]
    simp
  have hq_b : q b = 0 := by
    dsimp [q]
    simp [hne.symm]
  have hq_other (i : ι) (hi_a : i ≠ a) (hi_b : i ≠ b) : q i = p i := by
    dsimp [q]
    simp [hi_a, hi_b]
  -- Core inequality applied to p a and p b.
  have hineq : p a * Real.log (p a) + p b * Real.log (p b) < (p a + p b) * Real.log (p a + p b) :=
    mul_log_add_mul_log_lt_mul_log_add ha_pos hb_pos
  -- b is also in s.erase a since a ≠ b.
  have hb_erase : b ∈ s.erase a :=
    Finset.mem_erase_of_ne_of_mem hne.symm hb
  -- Decompose the sum over s by erasing a and b.
  have hp_sum_erase_a : Finset.sum s (fun i => p i * Real.log (p i)) =
      (p a * Real.log (p a)) + Finset.sum (s.erase a) (fun i => p i * Real.log (p i)) := by
    rw [← Finset.sum_erase_add s (fun i => p i * Real.log (p i)) ha]
    rw [add_comm]
  have hp_sum_erase_b : Finset.sum (s.erase a) (fun i => p i * Real.log (p i)) =
      (p b * Real.log (p b)) + Finset.sum ((s.erase a).erase b) (fun i => p i * Real.log (p i))
      := by
    rw [← Finset.sum_erase_add (s.erase a) (fun i => p i * Real.log (p i)) hb_erase]
    rw [add_comm]
  have hp_full : Finset.sum s (fun i => p i * Real.log (p i)) =
      (p a * Real.log (p a) + p b * Real.log (p b)) + Finset.sum ((s.erase a).erase b)
      (fun i => p i * Real.log (p i)) := by
    rw [hp_sum_erase_a, hp_sum_erase_b]
    ring
  have hq_sum_erase_a : Finset.sum s (fun i => q i * Real.log (q i)) =
      (q a * Real.log (q a)) + Finset.sum (s.erase a) (fun i => q i * Real.log (q i)) := by
    rw [← Finset.sum_erase_add s (fun i => q i * Real.log (q i)) ha]
    rw [add_comm]
  have hq_sum_erase_b : Finset.sum (s.erase a) (fun i => q i * Real.log (q i)) =
      (q b * Real.log (q b)) + Finset.sum ((s.erase a).erase b) (fun i => q i * Real.log (q i))
      := by
    rw [← Finset.sum_erase_add (s.erase a) (fun i => q i * Real.log (q i)) hb_erase]
    rw [add_comm]
  have hq_full : Finset.sum s (fun i => q i * Real.log (q i)) =
      (q a * Real.log (q a) + q b * Real.log (q b)) + Finset.sum ((s.erase a).erase b)
      (fun i => q i * Real.log (q i)) := by
    rw [hq_sum_erase_a, hq_sum_erase_b]
    ring
  -- Simplify q a and q b terms in hq_full: q b = 0 so its term is 0.
  rw [hq_a, hq_b] at hq_full
  simp only [Real.log_zero, mul_zero, add_zero] at hq_full
  -- On the set (s \ {a,b}), p and q agree, so their sums are equal.
  have hrest_eq : Finset.sum ((s.erase a).erase b) (fun i => p i * Real.log (p i)) =
      Finset.sum ((s.erase a).erase b) (fun i => q i * Real.log (q i)) :=
    Finset.sum_congr rfl fun i hi => by
      have hi_not_b : i ≠ b := Finset.ne_of_mem_erase hi
      have hi_not_a : i ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      simp [hq_other i hi_not_a hi_not_b]
  -- Combine to obtain the strict inequality of the sums: sum p log p < sum q log q.
  have hsum_ineq : Finset.sum s (fun i => p i * Real.log (p i)) <
  Finset.sum s (fun i => q i * Real.log (q i)) := by
    rw [hp_full, hq_full]
    rw [hrest_eq]
    linarith
  -- Entropy is the negative of the sum, so the inequality reverses.
  unfold entropy
  linarith

end TACG.ExampleApproach.EntropyDecreasesUnderEventMerging
