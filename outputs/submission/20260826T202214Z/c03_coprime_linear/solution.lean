import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h₁ : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by
    have h₂ : 9 * n + 4 = 4 * (2 * n + 1) + n := by
      ring
    rw [h₂, Nat.gcd_comm]
    simp [Nat.gcd_comm, Nat.add_comm, Nat.add_left_comm]
    <;> rw [Nat.gcd_assoc, Nat.gcd_comm]
    <;> simp [Nat.gcd_comm]
  
  have h₃ : Nat.gcd (2 * n + 1) n = Nat.gcd 1 n := by
    have h₄ : 2 * n + 1 = 2 * n + 1 := rfl
    have h₅ : Nat.gcd (2 * n + 1) n = Nat.gcd (2 * n + 1 - 2 * n) n := by
      rw [show 2 * n + 1 = 2 * n + 1 by rfl]
      rw [← Nat.sub_add_cancel (by omega : 2 * n ≤ 2 * n + 1)]
      simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
    rw [h₅]
    norm_num
    <;> simp [Nat.gcd_comm]
  
  have h₆ : Nat.gcd 1 n = 1 := by
    simp [Nat.gcd_one_left]
  
  calc
    Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := h₁
    _ = Nat.gcd 1 n := h₃
    _ = 1 := h₆
