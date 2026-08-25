import Mathlib

/-- Powers of two cycle mod 23 with period 11. -/
lemma h02_pow_mod (n : ℕ) : 2 ^ n % 23 = 2 ^ (n % 11) % 23 := by
  conv_lhs => rw [← Nat.div_add_mod n 11, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have key : 2 ^ n % 23 = 2 ^ (n % 11) % 23 := h02_pow_mod n
  have h11 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨
      n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
    omega
  rcases h11 with h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] at key <;> norm_num at key <;> omega

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  have key : 2 ^ n % 23 = 2 ^ (n % 11) % 23 := h02_pow_mod n
  have h11 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨
      n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
    omega
  rcases h11 with h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] at key <;> norm_num at key <;> omega
