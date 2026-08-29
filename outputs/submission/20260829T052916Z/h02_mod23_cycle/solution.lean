import Mathlib

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by sorry

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by sorry

-- Helper: 2^11 ≡ 1 (mod 23)
lemma pow_11_mod_23 : 2 ^ 11 % 23 = 1 := by norm_num

-- Helper: 2^m mod 23 for m in [1,10] are never 1
lemma pow_lt_11_neq_one (m : ℕ) (h1 : 0 < m) (h2 : m ≤ 10) : 2 ^ m % 23 ≠ 1 := by sorry

-- Helper: 2^m mod 23 for m in [1,20] are never 22
lemma pow_lt_21_neq_22 (m : ℕ) (h1 : 0 < m) (h2 : m ≤ 20) : 2 ^ m % 23 ≠ 22 := by sorry

-- Helper: If 23 | 2^n - 1 then 11 | n
lemma dvd_sub_implies_div_n (n : ℕ) (h : 23 ∣ 2 ^ n - 1) : 11 ∣ n := by sorry

-- Helper: If 11 | n then 23 | 2^n - 1
lemma div_n_implies_dvd_sub (n : ℕ) (h : 11 ∣ n) : 23 ∣ 2 ^ n - 1 := by sorry

-- Helper: 2^(2*n) ≡ 1 (mod 23) implies 2^n ≡ ±1 (mod 23)
lemma sq_eq_one_implies_eq_pm_one {n : ℕ} (h : 2 ^ (2 * n) % 23 = 1) : 2 ^ n % 23 = 1 ∨ 2 ^ n % 23 = 22 := by sorry

-- Helper: 23 does not divide 2^n + 1 for n in [1,20]
lemma no_plus_one_small (n : ℕ) (hn1 : 0 < n) (hn2 : n ≤ 20) : ¬23 ∣ 2 ^ n + 1 := by exact?
