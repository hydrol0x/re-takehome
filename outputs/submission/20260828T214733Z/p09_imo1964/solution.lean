import Mathlib

/-- Helper: n % 3 = 0 implies 3 divides n -/
lemma zero_mod_three_implies_three_div (n : ℕ) : n % 3 = 0 → 3 ∣ n := by omega

/-- Helper: 3 divides n implies n % 3 = 0 -/
lemma three_div_implies_zero_mod_three (n : ℕ) : 3 ∣ n → n % 3 = 0 := by omega

/-- Helper: Divisibility of 2^n + 1 by 7 iff mod is 0 -/
lemma div_two_pow_add_one_iff_mod_eq_zero (n : ℕ) : 7 ∣ 2 ^ n + 1 ↔ (2 ^ n + 1) % 7 = 0 := by omega

/-- Helper: Divisibility of 2^n - 1 by 7 iff mod is 0 -/
lemma div_two_pow_minus_one_iff_mod_eq_zero (n : ℕ) : 7 ∣ 2 ^ n - 1 ↔ (2 ^ n - 1) % 7 = 0 := by omega

/-- Helper: Periodicity of 2^n modulo 7 -/
lemma pow_two_mod_7_cycle (n : ℕ) : (2 ^ n) % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by sorry

/-- Helper: Powers of 2 are at least 1 -/
lemma two_pow_ge_one (n : ℕ) : 1 ≤ 2 ^ n := by exact?

/-- Helper: Relates (2^n - 1) % 7 = 0 to 2^n % 7 = 1 -/
lemma two_pow_minus_one_mod_7_iff_one (n : ℕ) (h : 1 ≤ 2 ^ n) : (2 ^ n - 1) % 7 = 0 ↔ 2 ^ n % 7 = 1 := by omega

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_ge : 1 ≤ 2 ^ n := two_pow_ge_one n
  rw [div_two_pow_minus_one_iff_mod_eq_zero]
  rw [two_pow_minus_one_mod_7_iff_one _ h_ge]
  rw [pow_two_mod_7_cycle]
  split_ifs <;> simp_all [zero_mod_three_implies_three_div, three_div_implies_zero_mod_three]
  <;> try { contradiction }
  <;> try { omega }
  <;> try { aesop }

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_ge : 1 ≤ 2 ^ n := two_pow_ge_one n
  rw [div_two_pow_add_one_iff_mod_eq_zero] at h
  have h_mod : (2 ^ n + 1) % 7 = ((2 ^ n) % 7 + 1) % 7 := by
    rw [← Nat.mod_add_div (2 ^ n) 7]
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
    <;> ring_nf
    <;> norm_num
  rw [h_mod] at h
  have h_cycle : (2 ^ n) % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := pow_two_mod_7_cycle n
  rw [h_cycle] at h
  split_ifs at h <;> norm_num at h <;> omega
