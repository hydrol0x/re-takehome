import Mathlib

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- Pattern of `2^n mod 7`. -/
lemma pow_mod_7_pattern (n : ℕ) : 2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by
  induction n with
  | zero => simp
  | succ n IH =>
    have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h_cases with h | h | h <;>
      simp [h, pow_succ, Nat.mul_mod, Nat.add_mod] at IH ⊢ <;>
      norm_num <;> omega

/-- Helper for (a): `7 ∣ 2^n - 1` iff `2^n % 7 = 1`. -/
lemma dvd_pow_minus_one_iff_mod_one (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by sorry

/-- Helper for (b): `7 ∣ 2^n + 1` iff `2^n % 7 = 6`. -/
lemma dvd_pow_plus_one_iff_mod_six (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n + 1 ↔ 2 ^ n % 7 = 6 := by omega

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  rw [dvd_pow_minus_one_iff_mod_one n hn]
  rw [pow_mod_7_pattern]
  constructor
  · intro h
    have h_mod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h_mod with h_mod | h_mod | h_mod <;>
      simp [h_mod, Nat.mod_eq_of_lt] at h ⊢ <;>
      omega
  · intro h
    have h_mod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h_mod with h_mod | h_mod | h_mod <;>
      simp [h_mod, Nat.mod_eq_of_lt] at h ⊢ <;>
      omega

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h₁ : 2 ^ n % 7 = 6 := by
    rw [dvd_pow_plus_one_iff_mod_six n hn] at h
    exact h
  have h_mod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_mod with h_mod | h_mod | h_mod <;>
    simp [h_mod, pow_mod_7_pattern] at h₁ <;>
    omega
