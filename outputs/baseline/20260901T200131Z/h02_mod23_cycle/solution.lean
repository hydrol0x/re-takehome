import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  constructor
  · intro h
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at h
    have h_order : orderOf (2 : ZMod 23) = 11 := by
      norm_num [orderOf_eq_prime_iff_pow_eq_one]
      decide
    rw [← h_order] at *
    exact Nat.dvd_of_mod_eq_zero (by
      have : (2 : ZMod 23) ^ n = 1 := by simpa using h
      simp_all [orderOf_dvd_iff_pow_eq_one])
  · intro h
    obtain ⟨k, rfl⟩ := h
    rw [pow_mul]
    have h_order : orderOf (2 : ZMod 23) = 11 := by
      norm_num [orderOf_eq_prime_iff_pow_eq_one]
      decide
    simp [h_order]
    exact ZMod.natCast_zmod_eq_zero_iff_dvd.mpr (by norm_num)

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  intro h
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at h
  simp_all [pow_add, pow_mul]
  have h_order : orderOf (2 : ZMod 23) = 11 := by
    norm_num [orderOf_eq_prime_iff_pow_eq_one]
    decide
  revert h
  induction' hn with n hn IH
  · norm_num
  · simp_all [pow_succ]
    norm_num
    decide
