import Mathlib

/-- 2^11 ≡ 1 (mod 23) -/
lemma pow_2_11_mod_23 : 2 ^ 11 % 23 = 1 := by norm_num

/-- If 11 | n, then 2^n ≡ 1 (mod 23) -/
lemma pow_2_mod_23_of_dvd_11 : ∀ n, 11 ∣ n → 2 ^ n % 23 = 1 := by sorry

/-- 2^k ≢ 1 (mod 23) for 0 < k < 11 -/
lemma pow_2_mod_23_neq_one_lt_11 : ∀ k, 0 < k → k < 11 → 2 ^ k % 23 ≠ 1 := by sorry

/-- 2^n ≡ 1 (mod 23) iff 11 | n -/
lemma pow_2_mod_23_eq_one_iff : ∀ n, 2 ^ n % 23 = 1 ↔ 11 ∣ n := by sorry

/-- 2^n ≢ 22 (mod 23) for any n -/
lemma pow_2_mod_23_neq_22 : ∀ n, 2 ^ n % 23 ≠ 22 := by sorry

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  sorry

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  sorry
