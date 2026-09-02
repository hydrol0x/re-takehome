import Mathlib

/-- `∑_{i=0}^{n-1} i * 2 ^ i = (n - 2) * 2 ^ n + 2` as integers. -/
theorem m07_sumgeo (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℤ) * 2 ^ i = ((n : ℤ) - 2) * 2 ^ n + 2 := by
  induction' n with n ih
  · -- Base case: n = 0
    simp [Finset.sum_range_zero]
  · -- Inductive step: assume true for n, prove for n + 1
    rw [Finset.sum_range_succ, ih]
    simp [pow_succ, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
    ring_nf
    <;> norm_cast
    <;> simp_all [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    <;> ring_nf at *
    <;> omega
