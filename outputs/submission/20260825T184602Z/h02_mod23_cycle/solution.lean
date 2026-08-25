import Mathlib

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by sorry

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by sorry

-- Helper: compute 2^11 mod 23 explicitly
lemma pow2_11_mod_23 : (2 ^ 11) % 23 = 1 := by
  norm_num

-- Helper: 2^n mod 23 depends on n mod 11
lemma pow2_mod_cycle (n : ℕ) : (2 ^ n) % 23 = (2 ^ (n % 11)) % 23 := by sorry

-- Helper: 2^k mod 23 for k < 11
lemma pow2_lt_11_mod_23 (k : ℕ) (hk : k < 11) : (2 ^ k) % 23 = 
  [1, 2, 4, 8, 16, 9, 18, 13, 3, 6, 12] !! k := by sorry

-- Helper: 2^k mod 23 is never 22 for any k
lemma pow2_neq_neg_one_mod_23 (k : ℕ) : (2 ^ k) % 23 ≠ 22 := by sorry

-- Helper: 2^n ≡ 1 (mod 23) iff 11 | n
lemma two_pow_eq_one_mod_23_iff (n : ℕ) : (2 ^ n) % 23 = 1 ↔ 11 ∣ n := by sorry

-- Helper: 2^n - 1 is divisible by 23 iff 2^n ≡ 1 (mod 23)
lemma sub_one_divisible_iff_equiv_one (n : ℕ) : 23 ∣ 2 ^ n - 1 ↔ (2 ^ n) % 23 = 1 := by sorry

-- Helper: 2^n + 1 is divisible by 23 iff 2^n ≡ 22 (mod 23)
lemma add_one_divisible_iff_equiv_22 (n : ℕ) : 23 ∣ 2 ^ n + 1 ↔ (2 ^ n) % 23 = 22 := by sorry
