import Mathlib

/-- Powers of 2 with exponent divisible by 3 are ≡ 1 (mod 7) -/
lemma pow_two_mul_three_mod_seven (k : ℕ) : 2 ^ (3 * k) % 7 = 1 := by sorry

/-- Powers of 2 with exponent ≡ 1 (mod 3) are ≡ 2 (mod 7) -/
lemma pow_two_mul_three_add_one_mod_seven (k : ℕ) : 2 ^ (3 * k + 1) % 7 = 2 := by sorry

/-- Powers of 2 with exponent ≡ 2 (mod 3) are ≡ 4 (mod 7) -/
lemma pow_two_mul_three_add_two_mod_seven (k : ℕ) : 2 ^ (3 * k + 2) % 7 = 4 := by sorry

/-- For any n, 2^n ≡ 1 (mod 7) iff 3 | n -/
lemma pow_two_mod_seven_eq_one_iff (n : ℕ) : 2 ^ n % 7 = 1 ↔ 3 ∣ n := by sorry

/-- For any n, 2^n + 1 ≡ 0 (mod 7) never holds -/
lemma pow_two_add_one_not_cong_zero_mod_seven (n : ℕ) : (2 ^ n + 1) % 7 ≠ 0 := by sorry

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by sorry

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by sorry
