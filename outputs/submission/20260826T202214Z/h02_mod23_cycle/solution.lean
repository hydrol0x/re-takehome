import Mathlib.Tactic

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by sorry

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by sorry

-- Helper lemmas for part (a)

lemma pow_23_mod_1 : (2 ^ 1 : ℤ) % 23 = 2 := by norm_num

lemma pow_23_mod_2 : (2 ^ 2 : ℤ) % 23 = 4 := by norm_num

lemma pow_23_mod_3 : (2 ^ 3 : ℤ) % 23 = 8 := by norm_num

lemma pow_23_mod_4 : (2 ^ 4 : ℤ) % 23 = 16 := by norm_num

lemma pow_23_mod_5 : (2 ^ 5 : ℤ) % 23 = 9 := by norm_num

lemma pow_23_mod_6 : (2 ^ 6 : ℤ) % 23 = 18 := by norm_num

lemma pow_23_mod_7 : (2 ^ 7 : ℤ) % 23 = 13 := by norm_num

lemma pow_23_mod_8 : (2 ^ 8 : ℤ) % 23 = 3 := by norm_num

lemma pow_23_mod_9 : (2 ^ 9 : ℤ) % 23 = 6 := by norm_num

lemma pow_23_mod_10 : (2 ^ 10 : ℤ) % 23 = 12 := by norm_num

lemma pow_23_mod_11 : (2 ^ 11 : ℤ) % 23 = 1 := by norm_num

lemma pow_23_mod_cycle {n : ℕ} : (2 ^ n : ℤ) % 23 = (2 ^ (n % 11) : ℤ) % 23 := by sorry

lemma pow_23_mod_0 : (2 ^ 0 : ℤ) % 23 = 1 := by norm_num

lemma pow_23_minus_1_iff_11_dvd {n : ℕ} : 23 ∣ (2 ^ n - 1 : ℤ) ↔ 11 ∣ n := by sorry

lemma pow_23_plus_1_neq_0 {n : ℕ} : ¬(2 ^ n + 1 : ℤ) % 23 = 0 := by sorry
