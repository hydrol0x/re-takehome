import Mathlib

/-- The value of `2 ^ n % 7` cycles with period 3. -/
lemma pow_mod_7_pattern (n : ℕ) : 2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by sorry

/-- `7 ∣ 2 ^ n - 1` is equivalent to `2 ^ n ≡ 1 (mod 7)` for `n > 0`. -/
lemma dvd_pow_minus_one_iff_mod (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by sorry

/-- `7 ∣ 2 ^ n + 1` is equivalent to `2 ^ n ≡ 6 (mod 7)` for `n > 0`. -/
lemma dvd_pow_plus_one_iff_mod (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n + 1 ↔ 2 ^ n % 7 = 6 := by omega

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · intro h
    have h_mod : 2 ^ n % 7 = 1 := by
      rw [dvd_pow_minus_one_iff_mod n hn] at h
      exact h
    have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h_cases with h | h | h
    · -- n % 3 = 0
      exact Nat.dvd_iff_mod_eq_zero.mpr h
    · -- n % 3 = 1
      have h_val : 2 ^ n % 7 = 2 := by
        rw [pow_mod_7_pattern]
        simp [h]
      linarith [h_mod, h_val]
    · -- n % 3 = 2
      have h_val : 2 ^ n % 7 = 4 := by
        rw [pow_mod_7_pattern]
        simp [h]
      linarith [h_mod, h_val]
  · intro h
    have h_mod : n % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    have h_val : 2 ^ n % 7 = 1 := by
      rw [pow_mod_7_pattern]
      simp [h_mod]
    rw [dvd_pow_minus_one_iff_mod n hn]
    exact h_val

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : 2 ^ n % 7 = 6 := by
    rw [dvd_pow_plus_one_iff_mod n hn] at h
    exact h
  have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_cases with h | h | h
  · -- n % 3 = 0
    have h_val : 2 ^ n % 7 = 1 := by
      rw [pow_mod_7_pattern]
      simp [h]
    linarith [h_mod, h_val]
  · -- n % 3 = 1
    have h_val : 2 ^ n % 7 = 2 := by
      rw [pow_mod_7_pattern]
      simp [h]
    linarith [h_mod, h_val]
  · -- n % 3 = 2
    have h_val : 2 ^ n % 7 = 4 := by
      rw [pow_mod_7_pattern]
      simp [h]
    linarith [h_mod, h_val]
