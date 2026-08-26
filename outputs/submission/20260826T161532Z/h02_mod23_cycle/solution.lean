import Mathlib

/-- Compute 2^11 mod 23 equals 1 -/
lemma pow_2_11_mod_23 : (2 ^ 11) % 23 = 1 := by norm_num

/-- Periodicity: 2^(m + 11) ≡ 2^m (mod 23) for any m -/
lemma pow_2_period_11 (m : ℕ) : (2 ^ (m + 11)) % 23 = (2 ^ m) % 23 := by rw [pow_add, Nat.mul_mod, pow_2_11_mod_23, Nat.mul_one, Nat.mod_mod]

/-- Base cases: for k < 11, 2^k ≡ 1 (mod 23) iff 11 | k -/
lemma pow_2_base_cases (k : ℕ) (hk : k < 11) : (2 ^ k) % 23 = 1 ↔ 11 ∣ k := by interval_cases k <;> norm_num [Nat.mod_eq_of_lt]

/-- For any n, 2^n ≡ 2^(n % 11) (mod 23) -/
lemma pow_2_mod_exp (n : ℕ) : (2 ^ n) % 23 = (2 ^ (n % 11)) % 23 := by sorry

/-- Divisibility by 23 equivalent to mod 23 being 0 -/
lemma dvd_iff_mod_eq_zero (a b : ℕ) : b ∣ a ↔ a % b = 0 := by omega

/-- For positive n: 23 | (2^n - 1) iff 2^n ≡ 1 (mod 23) -/
lemma sub_one_dvd_iff_mod (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ (2 ^ n) % 23 = 1 := by sorry

/-- For positive n: 23 | (2^n + 1) iff 2^n ≡ 22 (mod 23) -/
lemma add_one_dvd_iff_mod (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n + 1 ↔ (2 ^ n) % 23 = 22 := by omega

/-- Part (a): 23 | 2^n - 1 iff 11 | n for positive n -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by sorry

/-- Part (b): no positive n has 23 | 2^n + 1 -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by sorry
