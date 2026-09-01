import Mathlib

/-- The sum of the first `n` odd numbers is `n ^ 2`. -/
theorem c04_sum_odds (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        ∑ k ∈ Finset.range (n + 1), (2 * k + 1)
            = (∑ k ∈ Finset.range n, (2 * k + 1)) + (2 * n + 1) := by
              simpa using (Finset.sum_range_succ (fun k => 2 * k + 1) n)
        _ = n ^ 2 + (2 * n + 1) := by
              simpa [ih]
        _ = (n + 1) ^ 2 := by
              ring
