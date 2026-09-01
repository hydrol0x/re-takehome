import Mathlib

/-- `∑_{i=0}^{n-1} i * 2 ^ i = (n - 2) * 2 ^ n + 2` as integers. -/
theorem m07_sumgeo (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℤ) * 2 ^ i = ((n : ℤ) - 2) * 2 ^ n + 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      norm_num [Finset.sum_range_zero]
    | n + 1 =>
      have := ih n (by omega)
      simp [Finset.sum_range_succ, pow_succ, ← Int.mul_assoc] at this ⊢
      ring_nf at this ⊢
      <;> omega
