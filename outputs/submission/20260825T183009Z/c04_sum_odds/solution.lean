import Mathlib

/-- The sum of the first `n` odd numbers is `n ^ 2`. -/
theorem c04_sum_odds (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp [pow_succ, Nat.mul_succ] at ih ⊢
    ring_nf at ih ⊢
    omega
