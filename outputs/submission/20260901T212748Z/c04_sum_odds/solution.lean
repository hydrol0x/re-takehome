import Mathlib

/-- The sum of the first `n` odd numbers is `n ^ 2`. -/
theorem c04_sum_odds (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp [ih, pow_succ, mul_add, add_mul]
    ring_nf
