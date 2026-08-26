import Mathlib

/-- Powers of 2 with exponent divisible by 3 are ≡ 1 (mod 7) -/
lemma pow_two_mul_three_mod_seven (k : ℕ) : 2 ^ (3 * k) % 7 = 1 := by induction k with
| zero => norm_num
| succ k ih => 
have h₁ : 2 ^ 3 % 7 = 1 := by norm_num
have h₂ : (2 ^ (3 * k) * 2 ^ 3) % 7 = (2 ^ (3 * k) % 7) * (2 ^ 3 % 7) % 7 := by simp [Nat.mul_mod]
calc
  2 ^ (3 * (k + 1)) % 7 = 2 ^ (3 * k + 3) % 7 := by rw [show 3 * (k + 1) = 3 * k + 3 by ring]
  _ = (2 ^ (3 * k) * 2 ^ 3) % 7 := by rw [pow_add]
  _ = ((2 ^ (3 * k) % 7) * (2 ^ 3 % 7)) % 7 := by rw [h₂]
  _ = 1 * 1 % 7 := by rw [ih, h₁]
  _ = 1 := by norm_num

/-- Powers of 2 with exponent ≡ 1 (mod 3) are ≡ 2 (mod 7) -/
lemma pow_two_mul_three_add_one_mod_seven (k : ℕ) : 2 ^ (3 * k + 1) % 7 = 2 := by induction k with
| zero => norm_num
| succ k ih =>
  have h₁ : 2 ^ 3 % 7 = 1 := by norm_num
  calc
    2 ^ (3 * (k + 1) + 1) % 7 = 2 ^ (3 * k + 1 + 3) % 7 := by rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 3 by ring]
    _ = (2 ^ (3 * k + 1) * 2 ^ 3) % 7 := by rw [pow_add]
    _ = ((2 ^ (3 * k + 1) % 7) * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
    _ = (2 * 1) % 7 := by rw [ih, h₁]
    _ = 2 := by norm_num

/-- Powers of 2 with exponent ≡ 2 (mod 3) are ≡ 4 (mod 7) -/
lemma pow_two_mul_three_add_two_mod_seven (k : ℕ) : 2 ^ (3 * k + 2) % 7 = 4 := by induction k with
  | zero => norm_num
  | succ k ih =>
    have h₁ : 2 ^ 3 % 7 = 1 := by norm_num
    calc
      2 ^ (3 * (k + 1) + 2) % 7
        = 2 ^ (3 * k + 2 + 3) % 7 := by rw [show 3 * (k + 1) + 2 = 3 * k + 2 + 3 by ring]
      _ = (2 ^ (3 * k + 2) * 2 ^ 3) % 7 := by rw [pow_add]
      _ = ((2 ^ (3 * k + 2) % 7) * (2 ^ 3 % 7)) % 7 := by rw [Nat.mul_mod]
      _ = (4 * 1) % 7 := by rw [ih, h₁]
      _ = 4 := by norm_num

/-- For any n, 2^n ≡ 1 (mod 7) iff 3 | n -/
lemma pow_two_mod_seven_eq_one_iff (n : ℕ) : 2 ^ n % 7 = 1 ↔ 3 ∣ n := by -- Transform goal to use n % 3 = 0 instead of 3 ∣ n
  rw [Nat.dvd_iff_mod_eq_zero]
  constructor
  · -- Forward: 2^n % 7 = 1 → n % 3 = 0
    intro h
    have h_mod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h_mod with (h_mod | h_mod | h_mod)
    · assumption
    · -- n % 3 = 1 implies 2^n % 7 = 2
      have h_eq : n = 3 * (n / 3) + 1 := by omega
      rw [h_eq] at h
      have h_val : 2 ^ (3 * (n / 3) + 1) % 7 = 2 := pow_two_mul_three_add_one_mod_seven (n / 3)
      rw [h_val] at h
      omega
    · -- n % 3 = 2 implies 2^n % 7 = 4
      have h_eq : n = 3 * (n / 3) + 2 := by omega
      rw [h_eq] at h
      have h_val : 2 ^ (3 * (n / 3) + 2) % 7 = 4 := pow_two_mul_three_add_two_mod_seven (n / 3)
      rw [h_val] at h
      omega
  · -- Backward: n % 3 = 0 → 2^n % 7 = 1
    intro h
    have h_eq : n = 3 * (n / 3) := by omega
    rw [h_eq]
    exact pow_two_mul_three_mod_seven (n / 3)

/-- For any n, 2^n + 1 ≡ 0 (mod 7) never holds -/
lemma pow_two_add_one_not_cong_zero_mod_seven (n : ℕ) : (2 ^ n + 1) % 7 ≠ 0 := by sorry

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by sorry

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by sorry
