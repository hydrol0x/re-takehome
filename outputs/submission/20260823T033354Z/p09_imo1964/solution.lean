import Mathlib

-- Helper lemmas

/-- For any `n`, `(2 ^ n) % 7 = 1` iff `3 ∣ n`. -/
lemma pow_two_mod_seven_eq_one_iff_three_dvd (n : ℕ) :
    (2 ^ n) % 7 = 1 ↔ 3 ∣ n := by
  sorry

/-- For any `n`, `(2 ^ n) % 7` is never `6`. -/
lemma pow_two_mod_seven_not_eq_six (n : ℕ) :
    (2 ^ n) % 7 ≠ 6 := by
  sorry

/-- For any `n`, `7 ∣ 2 ^ n - 1` iff the remainder of `2 ^ n` modulo `7` equals `1`. -/
lemma seven_dvd_sub_one_iff_mod_eq_one (n : ℕ) :
    (7 ∣ 2 ^ n - 1) ↔ (2 ^ n) % 7 = 1 := by
  sorry

/-- For any `n`, `7 ∣ 2 ^ n + 1` iff the remainder of `2 ^ n` modulo `7` equals `6`. -/
lemma seven_dvd_add_one_iff_mod_eq_six (n : ℕ) :
    (7 ∣ 2 ^ n + 1) ↔ (2 ^ n) % 7 = 6 := by
  omega

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h₁ := (seven_dvd_sub_one_iff_mod_eq_one n)
  have h₂ := (pow_two_mod_seven_eq_one_iff_three_dvd n)
  exact h₁.trans h₂

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have hmod : (2 ^ n) % 7 = 6 :=
    (seven_dvd_add_one_iff_mod_eq_six n).1 h
  exact (pow_two_mod_seven_not_eq_six n) hmod
