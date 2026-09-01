import Mathlib

/-- `∑_{i=0}^{n-1} i * 2 ^ i = (n - 2) * 2 ^ n + 2` as integers. -/
theorem m07_sumgeo (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℤ) * 2 ^ i = ((n : ℤ) - 2) * 2 ^ n + 2 := by
  induction' n with n ih
  · simp [Finset.sum_range_zero]
  · rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    simp [pow_succ, mul_assoc, mul_comm, mul_left_comm] at ih ⊢
    ring_nf at ih ⊢
    <;> linarith
