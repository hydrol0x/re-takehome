import Mathlib

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- 2^11 ≡ 1 (mod 23) -/
lemma pow_two_eleven_mod_23 : 2 ^ 11 % 23 = 1 := by norm_num

/-- For any n, 2^n ≡ 1 (mod 23) iff 11 divides n -/
lemma two_pow_cong_one_iff_dvd_11 (n : ℕ) : 2 ^ n % 23 = 1 ↔ 11 ∣ n := by sorry

/-- 2^n ≢ 22 (mod 23) for any n ≥ 1 -/
lemma two_pow_neq_twentytwo_mod_23 (n : ℕ) (hn : 0 < n) : 2 ^ n % 23 ≠ 22 := by sorry

/-- For positive n, 2^n - 1 is divisible by 23 iff 11 divides n -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by sorry

/-- For positive n, 2^n + 1 is never divisible by 23 -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by sorry
