import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h1 : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) (n + 1) := by sorry
  have h2 : Nat.gcd (2 * n + 1) (n + 1) = Nat.gcd 1 (n + 1) := by sorry
  have h3 : Nat.gcd 1 (n + 1) = 1 := by norm_num
  calc
    Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) (n + 1) := h1
    _ = Nat.gcd 1 (n + 1) := h2
    _ = 1 := h3
