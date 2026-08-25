import Mathlib

/-- `∑_{i=0}^{n-1} i * 2 ^ i = (n - 2) * 2 ^ n + 2` as integers. -/
theorem m07_sumgeo (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℤ) * 2 ^ i = ((n : ℤ) - 2) * 2 ^ n + 2 := by
  induction' n with n ih
  · -- Base case: n = 0
    simp [Finset.sum_range_zero]
  · -- Inductive step: assume true for n, prove for n + 1
    rw [Finset.sum_range_succ, ih]
    simp [pow_succ]
    ring_nf
    <;> norm_cast
    <;> ring_nf at *
    <;> omega
