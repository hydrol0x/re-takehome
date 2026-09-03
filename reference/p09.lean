import Mathlib

/-- Powers of two cycle mod 7 with period 3. -/
lemma two_pow_mod_seven (n : ℕ) : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have key : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := two_pow_mod_seven n
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h | h | h <;> rw [h] at key <;> norm_num at key <;> omega

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  have key : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := two_pow_mod_seven n
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h | h | h <;> rw [h] at key <;> norm_num at key <;> omega
