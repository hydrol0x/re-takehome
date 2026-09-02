import Mathlib

set_option maxHeartbeats 1000000

-- Helper Lemma: Periodicity of 2^n mod 7
lemma pow_two_mod_7_periodic (n : ℕ) : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by sorry

-- Helper Lemma: Small power check (0, 1, 2)
lemma pow_two_small_mod_7_iff_zero (n : ℕ) (h : n < 3) : 2 ^ n % 7 = 1 ↔ n = 0 := by sorry

-- Helper Lemma: Characterization of 2^n ≡ 1 mod 7
lemma pow_two_mod_7_is_one_iff (n : ℕ) : 2 ^ n % 7 = 1 ↔ n % 3 = 0 := by sorry

-- Helper Lemma: Divisibility of 2^n - 1
lemma div_two_pow_sub_one_iff (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by sorry

-- Helper Lemma: 2^n mod 7 is never 6
lemma pow_two_mod_7_ne_six (n : ℕ) : 2 ^ n % 7 ≠ 6 := by sorry

-- Helper Lemma: Connection between (x+1)%7=0 and x%7=6
lemma mod_add_one_zero_iff (n : ℕ) : (n + 1) % 7 = 0 ↔ n % 7 = 6 := by omega

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by sorry

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by sorry
