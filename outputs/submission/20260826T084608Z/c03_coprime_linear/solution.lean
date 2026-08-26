import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h1 : 9 * n + 4 = n + 4 * (2 * n + 1) := by ring
  rw [h1]
  rw [Nat.gcd_add_mul_right_right]
  rw [Nat.gcd_comm]
  have h2 : 2 * n + 1 = 1 + 2 * n := by ring
  rw [h2]
  rw [Nat.gcd_add_mul_right_right]
  rw [Nat.gcd_one_right]
