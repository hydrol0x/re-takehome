import Mathlib

-- Helper: characterize 2^n mod 7 based on n mod 3
theorem pow_two_mod_seven (n : ℕ) : 2 ^ n % 7 = 
  if n % 3 = 0 then 1
  else if n % 3 = 1 then 2
  else 4 := by sorry

-- Helper: 7 divides 2^n - 1 iff 2^n ≡ 1 (mod 7)
theorem div_two_pow_minus_one_iff_mod_eq_one (n : ℕ) : 7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by sorry

-- Helper: 3 divides n iff n % 3 = 0
theorem three_dvd_iff_mod_zero (n : ℕ) : 3 ∣ n ↔ n % 3 = 0 := by omega

-- Main theorem (a): 7 ∣ 2^n - 1 ↔ 3 ∣ n
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_main : 2 ^ n % 7 = 1 ↔ n % 3 = 0 := by sorry
  calc
    7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by rw [div_two_pow_minus_one_iff_mod_eq_one]
    _ ↔ n % 3 = 0 := by rw [h_main]
    _ ↔ 3 ∣ n := by rw [three_dvd_iff_mod_zero]

-- Helper: 2^n + 1 mod 7 is never 0 for any n
theorem two_pow_plus_one_mod_seven_neq_zero (n : ℕ) : (2 ^ n + 1) % 7 ≠ 0 := by sorry

-- Main theorem (b): ¬7 ∣ 2^n + 1
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : (2 ^ n + 1) % 7 = 0 := by sorry
  exact two_pow_plus_one_mod_seven_neq_zero n h_mod
