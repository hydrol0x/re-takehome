import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h₁ : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by
    have h₁₁ : 9 * n + 4 = 4 * (2 * n + 1) + n := by
      ring
    rw [h₁₁]
    rw [Nat.gcd_comm]
    rw [← Nat.gcd_comm]
    rw [Nat.gcd_add_mul_right_right]
    <;> simp [Nat.gcd_comm]
  
  have h₂ : Nat.gcd (2 * n + 1) n = Nat.gcd 1 n := by
    have h₂₁ : 2 * n + 1 = 2 * n + 1 := rfl
    rw [← Nat.gcd_comm]
    rw [← Nat.gcd_comm]
    rw [Nat.gcd_add_mul_right_right]
    <;> simp [Nat.gcd_comm]
    <;> ring_nf
    <;> simp [Nat.gcd_comm]
  
  have h₃ : Nat.gcd 1 n = 1 := by
    simp [Nat.gcd_one_left]
  
  rw [h₁, h₂, h₃]
