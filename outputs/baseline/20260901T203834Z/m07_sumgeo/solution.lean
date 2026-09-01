import Mathlib

open Finset

/-- `∑_{i=0}^{n-1} i * 2 ^ i = (n - 2) * 2 ^ n + 2` as integers. -/
theorem m07_sumgeo (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℤ) * 2 ^ i = ((n : ℤ) - 2) * 2 ^ n + 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [pow_succ, mul_comm, mul_left_comm, mul_assoc] at *
      ring
