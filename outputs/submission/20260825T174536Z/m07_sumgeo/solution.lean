import Mathlib

/-- `∑_{i=0}^{n-1} i * 2 ^ i = (n - 2) * 2 ^ n + 2` as integers. -/
theorem m07_sumgeo (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℤ) * 2 ^ i = ((n : ℤ) - 2) * 2 ^ n + 2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    simp [pow_succ, mul_add, add_mul, mul_comm, mul_left_comm]
    ring_nf at *
    <;> simp_all [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
    <;> ring_nf at *
    <;> norm_num at *
    <;> linarith
