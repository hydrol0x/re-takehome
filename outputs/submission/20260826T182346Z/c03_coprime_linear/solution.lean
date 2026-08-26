import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h₁ : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) 1 := by
    -- Use the fact that gcd(a, b) = gcd(a, b - k*a) where k is chosen to eliminate n
    -- We need: 9n + 4 - k(2n + 1) = 1 for some k
    -- This gives us: 9n + 4 - 2kn - k = 1, so n(9 - 2k) = k - 3
    -- We want 9 - 2k = 0, so k = 4.5... not an integer
    -- Let's try k = 4: 9n + 4 - 4(2n + 1) = 9n + 4 - 8n - 4 = n
    -- So gcd(2n+1, 9n+4) = gcd(2n+1, n)
    rw [← Nat.gcd_comm]
    have h₂ : 9 * n + 4 = 4 * (2 * n + 1) + n := by ring
    rw [h₂]
    simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
    <;> simp_all [Nat.gcd_comm]
    <;> omega
  
  rw [h₁]
  simp [Nat.gcd_one_right]
