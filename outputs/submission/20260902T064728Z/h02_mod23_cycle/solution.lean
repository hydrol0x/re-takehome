import Mathlib

set_option maxHeartbeats 1000000

/-- Helper: Base case for the cycle of 2 modulo 23 -/
lemma h_helper_base : (2 ^ 11) % 23 = 1 := by norm_num

/-- Helper: Reduces 2^n mod 23 to 2^(n % 11) mod 23 -/
lemma h_helper_period (n : ℕ) : (2 ^ n) % 23 = (2 ^ (n % 11)) % 23 := by sorry

/-- Helper: Uniqueness of the residue 1 in the range 0 <= r < 11 -/
lemma h_helper_unique_1 (r : ℕ) (hr : r < 11) : (2 ^ r) % 23 = 1 ↔ r = 0 := by interval_cases r <;> norm_num

/-- Helper: No residue equals 22 in the range 0 <= r < 11 -/
lemma h_helper_unique_22 (r : ℕ) (hr : r < 11) : (2 ^ r) % 23 ≠ 22 := by interval_cases r <;> norm_num

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by sorry

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by sorry