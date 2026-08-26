import Mathlib

/-- Helper: 23 divides 2^11 - 1 -/
lemma h02_2_11_minus_1 : 23 ∣ 2^11 - 1 := by norm_num

/-- Helper: 23 does not divide 2^1 - 1 -/
lemma h02_r1 : ¬(23 ∣ 2^1 - 1) := by norm_num

/-- Helper: 23 does not divide 2^2 - 1 -/
lemma h02_r2 : ¬(23 ∣ 2^2 - 1) := by norm_num

/-- Helper: 23 does not divide 2^3 - 1 -/
lemma h02_r3 : ¬(23 ∣ 2^3 - 1) := by norm_num

/-- Helper: 23 does not divide 2^4 - 1 -/
lemma h02_r4 : ¬(23 ∣ 2^4 - 1) := by norm_num

/-- Helper: 23 does not divide 2^5 - 1 -/
lemma h02_r5 : ¬(23 ∣ 2^5 - 1) := by norm_num

/-- Helper: 23 does not divide 2^6 - 1 -/
lemma h02_r6 : ¬(23 ∣ 2^6 - 1) := by norm_num

/-- Helper: 23 does not divide 2^7 - 1 -/
lemma h02_r7 : ¬(23 ∣ 2^7 - 1) := by norm_num

/-- Helper: 23 does not divide 2^8 - 1 -/
lemma h02_r8 : ¬(23 ∣ 2^8 - 1) := by norm_num

/-- Helper: 23 does not divide 2^9 - 1 -/
lemma h02_r9 : ¬(23 ∣ 2^9 - 1) := by norm_num

/-- Helper: 23 does not divide 2^10 - 1 -/
lemma h02_r10 : ¬(23 ∣ 2^10 - 1) := by norm_num

/-- Helper: 11 divides 2*n iff 11 divides n -/
lemma h02_11_dvd_2n (n : ℕ) : 11 ∣ 2 * n ↔ 11 ∣ n := by omega

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  sorry

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  sorry
