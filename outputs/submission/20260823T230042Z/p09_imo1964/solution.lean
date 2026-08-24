import Mathlib

/-- Helper: `3 ∣ n ↔ n % 3 = 0`. -/
theorem three_dvd_iff_mod_zero (n : ℕ) : 3 ∣ n ↔ n % 3 = 0 := by
  omega

/-- Helper: `7 ∣ 2 ^ n - 1 ↔ (2 ^ n) % 7 = 1`. -/
theorem seven_dvd_sub_one_iff_mod_one (n : ℕ) :
    7 ∣ 2 ^ n - 1 ↔ (2 ^ n) % 7 = 1 := by
  constructor
  · intro h
    have : (2 ^ n) % 7 = 1 := by
      have : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
      have : (2 ^ n) % 7 = 1 := by
        have h₂ : 2 ^ n ≥ 1 := by apply Nat.one_le_pow <;> norm_num
        omega
      exact this
    assumption
  · intro h
    rw [← Nat.mod_add_div (2 ^ n) 7]
    simp [h, Nat.dvd_iff_mod_eq_zero]
    <;> omega

/-- Helper: `7 ∣ 2 ^ n + 1 ↔ (2 ^ n) % 7 = 6`. -/
theorem seven_dvd_add_one_iff_mod_six (n : ℕ) :
    7 ∣ 2 ^ n + 1 ↔ (2 ^ n) % 7 = 6 := by
  omega

/-- Helper: `(2 ^ n) % 7 = 1 ↔ 3 ∣ n`. -/
theorem two_pow_mod_seven_eq_one_iff_three_dvd (n : ℕ) :
    (2 ^ n) % 7 = 1 ↔ 3 ∣ n := by
  rw [← Nat.div_add_mod n 3]
  simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod]
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h <;> simp [h, pow_zero, one_pow, zero_pow, Nat.mod_eq_of_lt]
  <;> norm_num <;> omega

/-- Helper: `(2 ^ n) % 7 ≠ 6` for any `n`. -/
theorem two_pow_mod_seven_ne_six (n : ℕ) : (2 ^ n) % 7 ≠ 6 := by
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h <;>
    rw [← Nat.div_add_mod n 3] <;>
    simp [h, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.mod_mod] <;>
    norm_num <;> omega

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h₁ := (seven_dvd_sub_one_iff_mod_one (n := n))
  have h₂ := (two_pow_mod_seven_eq_one_iff_three_dvd (n := n))
  simpa using h₁.trans h₂

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have hmod : (2 ^ n) % 7 = 6 :=
    (seven_dvd_add_one_iff_mod_six (n := n)).1 h
  exact (two_pow_mod_seven_ne_six (n := n)) hmod
