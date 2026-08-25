import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h1 : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by sorry
  have h2 : Nat.gcd (2 * n + 1) n = 1 := by norm_num
  rw [h1, h2]
