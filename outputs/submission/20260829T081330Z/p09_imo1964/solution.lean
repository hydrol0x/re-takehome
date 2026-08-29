import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by sorry

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by sorry

-- Helper lemmas for part (a)

lemma dvd_sub_one_iff_mod_one (n : ℕ) : 7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by sorry

lemma mod_one_iff_three_dvd (n : ℕ) : 2 ^ n % 7 = 1 ↔ 3 ∣ n := by sorry

lemma mod_one_implies_dvd_sub_one (n : ℕ) (h : 2 ^ n % 7 = 1) : 7 ∣ 2 ^ n - 1 := by omega

lemma dvd_sub_one_implies_mod_one (n : ℕ) (h : 7 ∣ 2 ^ n - 1) : 2 ^ n % 7 = 1 := by exact?

-- Helper lemmas for part (b)

lemma mod_six_impossible : ∀ k r, 2 ^ (3 * k + r) % 7 ≠ 6 := by sorry

lemma no_plus_one_divisible : ∀ n, 2 ^ n % 7 ≠ 6 := by sorry

lemma not_dvd_plus_one (n : ℕ) (h : 7 ∣ 2 ^ n + 1) : 2 ^ n % 7 = 6 := by omega
