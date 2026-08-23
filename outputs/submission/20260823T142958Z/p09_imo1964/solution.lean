import Mathlib

-- ----------------------------------------------------------------------
-- Helper lemmas
-- ----------------------------------------------------------------------

/-- `7` divides `2 ^ n - 1` iff `2 ^ n` is congruent to `1` modulo `7`. -/
lemma seven_dvd_pow_sub_one_iff_mod_eq_one (n : ℕ) :
    7 ∣ 2 ^ n - 1 ↔ (2 ^ n) % 7 = 1 := by
  have h_ge : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
  rw [← Nat.mod_add_div (2 ^ n) 7]
  simp [h_ge, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_sub_assoc, Nat.add_sub_cancel]
  ring_nf
  omega

/-- `7` divides `2 ^ n + 1` iff `2 ^ n` is congruent to `6` modulo `7`. -/
lemma seven_dvd_pow_add_one_iff_mod_eq_six (n : ℕ) :
    7 ∣ 2 ^ n + 1 ↔ (2 ^ n) % 7 = 6 := by
  omega

/-- For any `k`, `2 ^ (3 * k) ≡ 1 (mod 7)`. -/
lemma pow_two_mod_seven_eq_one (k : ℕ) :
    (2 ^ (3 * k)) % 7 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.pow_add, Nat.pow_mul]
    simp [ih, Nat.mul_mod, Nat.pow_mod, pow_two_mod_seven_eq_one]
    <;> norm_num

/-- For any `k`, `2 ^ (3 * k + 1) ≡ 2 (mod 7)`. -/
lemma pow_two_mod_seven_eq_two (k : ℕ) :
    (2 ^ (3 * k + 1)) % 7 = 2 := by
  calc
    (2 ^ (3 * k + 1)) % 7 = ((2 ^ 3) ^ k * 2) % 7 := by
      rw [← pow_mul, pow_add]
      ring_nf
    _ = (((2 ^ 3) % 7) ^ k * (2 % 7)) % 7 := by
      simp [Nat.pow_mod, Nat.mul_mod]
    _ = (1 ^ k * 2) % 7 := by
      have h : (2 ^ 3) % 7 = 1 := by norm_num
      rw [h]
      <;> simp [Nat.one_pow]
    _ = 2 := by norm_num

/-- For any `k`, `2 ^ (3 * k + 2) ≡ 4 (mod 7)`. -/
lemma pow_two_mod_seven_eq_four (k : ℕ) :
    (2 ^ (3 * k + 2)) % 7 = 4 := by
  sorry

/-- If `2 ^ n ≡ 1 (mod 7)` then `3 ∣ n`. -/
lemma three_dvd_of_mod_one (n : ℕ) (h : (2 ^ n) % 7 = 1) : 3 ∣ n := by
  sorry

/-- For any `n`, `2 ^ n mod 7` is never `6`. -/
lemma pow_two_mod_seven_ne_six (n : ℕ) : (2 ^ n) % 7 ≠ 6 := by
  sorry

-- ----------------------------------------------------------------------
-- Main theorems
-- ----------------------------------------------------------------------

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · intro h7
    have hmod : (2 ^ n) % 7 = 1 :=
      (seven_dvd_pow_sub_one_iff_mod_eq_one n).mp h7
    exact three_dvd_of_mod_one n hmod
  · intro h3
    rcases h3 with ⟨k, hk⟩
    have hmod : (2 ^ n) % 7 = 1 := by
      have : (2 ^ (3 * k)) % 7 = 1 := pow_two_mod_seven_eq_one k
      simpa [hk] using this
    exact (seven_dvd_pow_sub_one_iff_mod_eq_one n).mpr hmod

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h7
  have hmod : (2 ^ n) % 7 = 6 :=
    (seven_dvd_pow_add_one_iff_mod_eq_six n).mp h7
  have hne : (2 ^ n) % 7 ≠ 6 := pow_two_mod_seven_ne_six n
  exact hne hmod
