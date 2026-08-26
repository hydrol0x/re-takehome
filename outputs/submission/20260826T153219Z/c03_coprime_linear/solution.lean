import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h₁ : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by
    have h₂ : 9 * n + 4 = 4 * (2 * n + 1) + n := by ring
    rw [h₂]
    rw [Nat.gcd_comm]
    simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
    <;> rw [Nat.gcd_comm]
  
  have h₃ : Nat.gcd (2 * n + 1) n = Nat.gcd 1 n := by
    have h₄ : 2 * n + 1 = 2 * n + 1 := rfl
    rw [show 2 * n + 1 = 2 * n + 1 by rfl]
    rw [Nat.gcd_comm]
    simp [Nat.gcd_comm, Nat.gcd_add_mul_left_right]
    <;> rw [Nat.gcd_comm]
  
  have h₅ : Nat.gcd 1 n = 1 := by
    simp [Nat.gcd_one_left]
  
  rw [h₁, h₃, h₅]
