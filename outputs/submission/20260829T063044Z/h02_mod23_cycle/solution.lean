import Mathlib

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  sorry

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  sorry

-- ==================== HELPER LEMMAS ====================

/-- The base case: 2^11 is congruent to 1 modulo 23. -/
lemma h_mod_base : 2 ^ 11 % 23 = 1 := by norm_num

/-- Powers of 2 modulo 23 repeat with period 11. -/
lemma h_mod_periodic : ∀ n : ℕ, 2 ^ (n + 11) % 23 = 2 ^ n % 23 := by sorry

/-- No power of 2 between 1 and 10 (exclusive) is congruent to 1 mod 23. -/
lemma h_mod_no_one_small : ∀ k : ℕ, 0 < k → k < 11 → 2 ^ k % 23 ≠ 1 := by sorry

/-- Relates 2^n % 23 = 1 to divisibility by 11. -/
lemma h_mod_eq_one_iff_div_11 : ∀ n : ℕ, 2 ^ n % 23 = 1 ↔ 11 ∣ n := by sorry

/-- 2^n is never congruent to 22 (which is -1) modulo 23. -/
lemma h_mod_neq_22 : ∀ n : ℕ, 2 ^ n % 23 ≠ 22 := by sorry

/-- Relates divisibility of (2^n - 1) by 23 to 2^n % 23 = 1. -/
lemma h_dvd_sub_iff_mod : ∀ n : ℕ, 23 ∣ 2 ^ n - 1 ↔ 2 ^ n % 23 = 1 := by sorry

/-- Relates divisibility of (2^n + 1) by 23 to 2^n % 23 = 22. -/
lemma h_dvd_add_iff_mod : ∀ n : ℕ, 23 ∣ 2 ^ n + 1 ↔ 2 ^ n % 23 = 22 := by omega
