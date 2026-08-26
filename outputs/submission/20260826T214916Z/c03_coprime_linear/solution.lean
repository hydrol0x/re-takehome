import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by calc
  Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) (n + 4 * (2 * n + 1)) := by
    rw [show 9 * n + 4 = n + 4 * (2 * n + 1) by ring]
  _ = Nat.gcd (2 * n + 1) n := by
    simp [Nat.gcd_add_mul_right_right, Nat.gcd_comm]
  _ = Nat.gcd 1 n := by
    simp [Nat.gcd_comm, Nat.gcd_add_mul_right_left]
  _ = 1 := by norm_num

lemma gcd_step1 (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by
  calc
    Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) (n + 4 * (2 * n + 1)) := by
      rw [show 9 * n + 4 = n + 4 * (2 * n + 1) by ring]
    _ = Nat.gcd (2 * n + 1) n := by
      rw [← Nat.gcd_comm]
      simp [Nat.gcd_add_mul_right_right, ← Nat.gcd_comm]

lemma gcd_step2 (n : ℕ) : Nat.gcd (2 * n + 1) n = Nat.gcd 1 n := by
  norm_num

lemma gcd_final (n : ℕ) : Nat.gcd 1 n = 1 := by
  norm_num
