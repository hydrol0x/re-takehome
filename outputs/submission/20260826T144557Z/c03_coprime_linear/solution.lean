import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  -- Helper: Show that gcd(2n+1, 9n+4) = gcd(2n+1, n)
  -- Proof: 9n+4 = 4*(2n+1) + n, so gcd(2n+1, 9n+4) = gcd(2n+1, n)
  have h1 : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by
    rw [show 9 * n + 4 = 4 * (2 * n + 1) + n by ring]
    rw [Nat.gcd_comm]
    simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
  
  -- Helper: Show that gcd(2n+1, n) = gcd(1, n)
  -- Proof: 2n+1 = 2*n + 1, so gcd(2n+1, n) = gcd(1, n)
  have h2 : Nat.gcd (2 * n + 1) n = Nat.gcd 1 n := by
    rw [show 2 * n + 1 = 2 * n + 1 by rfl]
    rw [Nat.gcd_comm]
    simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
  
  -- Helper: Show that gcd(1, n) = 1
  have h3 : Nat.gcd 1 n = 1 := by
    simp [Nat.gcd_one_left]
  
  -- Main proof: chain the equalities together
  rw [h1, h2, h3]
