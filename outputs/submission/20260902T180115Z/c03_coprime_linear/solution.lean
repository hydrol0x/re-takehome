import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  -- Reduce 9n + 4 modulo 2n + 1. 
  -- 9n + 4 = n + 4(2n + 1).
  rw [show 9 * n + 4 = n + 4 * (2 * n + 1) by ring]
  rw [Nat.gcd_add_mul_right_right]
  
  -- Swap arguments to reduce 2n + 1 modulo n.
  rw [Nat.gcd_comm]
  
  -- Reduce 2n + 1 modulo n.
  -- 2n + 1 = 1 + 2n.
  rw [show 2 * n + 1 = 1 + 2 * n by ring]
  rw [Nat.gcd_add_mul_right_right]
  
  -- gcd(n, 1) = 1.
  rw [Nat.gcd_one_right]
