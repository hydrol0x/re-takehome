import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by
    -- Use the property gcd(a, b) = gcd(a, b - k*a)
    have h1 : 9 * n + 4 = 4 * (2 * n + 1) + n := by ring
    rw [h1]
    -- gcd(a, b + k*a) = gcd(a, b) for any k
    rw [Nat.gcd_comm]
    simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
    <;> rw [Nat.gcd_comm]
    <;> simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
  
  rw [h]
  
  -- Now we need to show gcd(2n+1, n) = 1
  have h2 : Nat.gcd (2 * n + 1) n = Nat.gcd n 1 := by
    have h3 : 2 * n + 1 = 2 * n + 1 := rfl
    rw [Nat.gcd_comm]
    simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
    <;> rw [Nat.gcd_comm]
    <;> simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
    
  rw [h2]
  
  -- gcd(n, 1) = 1 for any n
  simp [Nat.gcd_one_right]
