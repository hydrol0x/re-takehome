import Mathlib

/-- The sum of the first `n` odd numbers is `n ^ 2`. -/
theorem c04_sum_odds (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [Finset.sum_range_succ, ih, Nat.succ_eq_add_one, pow_two] using
        (by
          ring)
