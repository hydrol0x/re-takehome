import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h1 : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by
    rw [← Nat.gcd_comm]
    rw [← Nat.gcd_comm]
    -- Use the property that gcd(a,b) = gcd(a, b - k*a)
    rw [show 9 * n + 4 = 4 * (2 * n + 1) + n by ring]
    simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
    <;> ring_nf at *
    <;> omega
  
  have h2 : Nat.gcd (2 * n + 1) n = Nat.gcd 1 n := by
    -- Use the property that gcd(a,b) = gcd(a - k*b, b)
    rw [← Nat.gcd_comm]
    rw [← Nat.gcd_comm]
    rw [show 2 * n + 1 = 2 * n + 1 by rfl]
    simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right, Nat.gcd_eq_right_iff_dvd]
    <;> ring_nf at *
    <;> omega
  
  have h3 : Nat.gcd 1 n = 1 := by
    simp [Nat.gcd_one_left]
  
  calc
    Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := h1
    _ = Nat.gcd 1 n := h2
    _ = 1 := h3
