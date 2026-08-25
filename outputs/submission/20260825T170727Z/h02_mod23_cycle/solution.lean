import Mathlib

-- Helper lemmas for modular arithmetic with base 2 and modulus 23

/-- Compute 2^11 mod 23 directly. -/
lemma h02_helpers_two_pow_11_mod_23 : 2 ^ 11 % 23 = 1 := by norm_num

/-- For any k strictly between 0 and 11, 2^k is not congruent to 1 mod 23. -/
lemma h02_helpers_no_smaller_power_is_one (k : ℕ) (hk_pos : 0 < k) (hk_lt : k < 11) : 2 ^ k % 23 ≠ 1 := by sorry

/-- If 11 divides n, then 2^n is congruent to 1 mod 23. -/
lemma h02_helpers_11_divides_implies_mod_1 (n : ℕ) (h : 11 ∣ n) : 2 ^ n % 23 = 1 := by sorry

/-- If 2^n is congruent to 1 mod 23, then 11 divides n. -/
lemma h02_helpers_mod_1_implies_11_divides (n : ℕ) (h : 2 ^ n % 23 = 1) : 11 ∣ n := by sorry

/-- 23 divides 2^n - 1 iff 2^n % 23 = 1. -/
lemma h02_helpers_div_iff_mod_1 (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 2 ^ n % 23 = 1 := by sorry

/-- 2^n % 23 is never 22 (which corresponds to -1 mod 23). -/
lemma h02_helpers_no_minus_one (n : ℕ) (hn : 0 < n) : 2 ^ n % 23 ≠ 22 := by sorry

-- Challenge theorems (statements kept byte-for-byte identical to challenge)

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by sorry

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by sorry
