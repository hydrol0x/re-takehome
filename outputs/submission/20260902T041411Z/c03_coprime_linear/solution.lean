import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h1 : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by
    have h1a : 9 * n + 4 = 4 * (2 * n + 1) + n := by ring
    rw [h1a]
    simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
  
  have h2 : Nat.gcd (2 * n + 1) n = 1 := by
    have h2a : 2 * n + 1 = 2 * n + 1 := rfl
    have h2b : Nat.gcd (2 * n + 1) n = Nat.gcd 1 n := by
      have h2c : 2 * n + 1 = 2 * n + 1 := rfl
      have h2d : Nat.gcd (2 * n + 1) n = Nat.gcd ((2 * n + 1) - 2 * n) n := by
        rw [← Nat.sub_add_cancel (by omega : 2 * n ≤ 2 * n + 1)]
        simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
      rw [h2d]
      <;> norm_num
      <;> omega
    rw [h2b]
    simp [Nat.gcd_one_left]
  
  rw [h1, h2]
