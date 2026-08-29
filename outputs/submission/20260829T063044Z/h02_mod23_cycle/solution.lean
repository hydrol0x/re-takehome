import Mathlib

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  sorry

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  sorry

-- Given helpers (included verbatim as specified)
lemma h_mod_base : 2 ^ 11 % 23 = 1 := by norm_num

lemma h_dvd_add_iff_mod : ∀ n : ℕ, 23 ∣ 2 ^ n + 1 ↔ 2 ^ n % 23 = 22 := by omega

lemma h_residue_ne_22_all : ∀ k, k < 11 → 2 ^ k % 23 ≠ 22 := by decide

-- Helper: period 11 property for powers of 2 mod 23
lemma h_pow_period_11 : ∀ m k : ℕ, 2 ^ (m * 11 + k) % 23 = 2 ^ k % 23 := by
  intro m k
  rw [pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  have h : (2 ^ m % 23) ^ 11 % 23 = 1 := by
    calc
      (2 ^ m % 23) ^ 11 % 23 = (2 ^ m) ^ 11 % 23 := by rw [← Nat.pow_mod]
      _ = 2 ^ (m * 11) % 23 := by rw [← pow_mul]
      _ = 2 ^ (11 * m) % 23 := by rw [mul_comm]
      _ = (2 ^ 11) ^ m % 23 := by rw [pow_mul]
      _ = (2 ^ 11 % 23) ^ m % 23 := by rw [Nat.pow_mod]
      _ = 1 ^ m % 23 := by rw [h_mod_base]
      _ = 1 % 23 := by simp [pow_one]
      _ = 1 := by norm_num
  rw [h]
  simp [Nat.mul_one, Nat.mod_mod]

-- Helper: 2^n ≡ 1 (mod 23) iff 11 | n
lemma h_pow_eq_one_iff_div_11 : ∀ n : ℕ, 2 ^ n % 23 = 1 ↔ 11 ∣ n := by
  sorry

-- Helper: 23 ∣ 2^n - 1 iff 2^n ≡ 1 (mod 23)
lemma h_dvd_sub_one_iff_mod_one : ∀ n : ℕ, 23 ∣ 2 ^ n - 1 ↔ 2 ^ n % 23 = 1 := by
  sorry
