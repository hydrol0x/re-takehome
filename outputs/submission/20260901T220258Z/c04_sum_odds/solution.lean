import Mathlib

/-- The sum of the first `n` odd numbers is `n ^ 2`. -/
theorem c04_sum_odds (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        ∑ k ∈ Finset.range (Nat.succ n), (2 * k + 1)
            = (∑ k ∈ Finset.range n, (2 * k + 1)) + (2 * n + 1) := by
              simpa [Finset.sum_range_succ]
        _ = n ^ 2 + (2 * n + 1) := by
              simpa [ih]
        _ = (n + 1) ^ 2 := by
              simpa [pow_two] using
                (by
                  ring : n * n + (2 * n + 1) = (n + 1) * (n + 1))
