import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.OrderOfElem

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  constructor
  · -- Forward direction: if 23 divides 2^n - 1, then 11 divides n
    intro h
    have h_mod : (2 : ZMod 23) ^ n = 1 := by
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at h
      simp_all [ZMod.natCast_zmod_eq_zero_iff_dvd]
    have h_order : orderOf (2 : ZMod 23) ∣ n := by
      apply pow_orderOf_eq_one_iff.mp
      exact h_mod
    have h_order_val : orderOf (2 : ZMod 23) = 11 := by
      -- Show that the order of 2 mod 23 is exactly 11
      have h1 : (2 : ZMod 23) ^ 11 = 1 := by
        norm_num [pow_succ, ZMod.natCast_zmod_eq_zero_iff_dvd]
      have h2 : ∀ k : ℕ, 0 < k → k < 11 → (2 : ZMod 23) ^ k ≠ 1 := by
        intro k hk_pos hk_lt
        interval_cases k <;> norm_num [pow_succ, ZMod.natCast_zmod_eq_zero_iff_dvd]
      exact orderOf_eq_prime_of_pow_eq_one h1 h2
    rw [h_order_val] at h_order
    exact h_order
  · -- Reverse direction: if 11 divides n, then 23 divides 2^n - 1
    intro h
    have h_order_val : orderOf (2 : ZMod 23) = 11 := by
      have h1 : (2 : ZMod 23) ^ 11 = 1 := by
        norm_num [pow_succ, ZMod.natCast_zmod_eq_zero_iff_dvd]
      have h2 : ∀ k : ℕ, 0 < k → k < 11 → (2 : ZMod 23) ^ k ≠ 1 := by
        intro k hk_pos hk_lt
        interval_cases k <;> norm_num [pow_succ, ZMod.natCast_zmod_eq_zero_iff_dvd]
      exact orderOf_eq_prime_of_pow_eq_one h1 h2
    have h_mod : (2 : ZMod 23) ^ n = 1 := by
      rw [← h_order_val]
      apply pow_orderOf_eq_one
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    simpa [ZMod.natCast_zmod_eq_zero_iff_dvd] using h_mod

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : (2 : ZMod 23) ^ n = -1 := by
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at h
    simp_all [ZMod.natCast_zmod_eq_zero_iff_dvd]
  have h_order_val : orderOf (2 : ZMod 23) = 11 := by
    have h1 : (2 : ZMod 23) ^ 11 = 1 := by
      norm_num [pow_succ, ZMod.natCast_zmod_eq_zero_iff_dvd]
    have h2 : ∀ k : ℕ, 0 < k → k < 11 → (2 : ZMod 23) ^ k ≠ 1 := by
      intro k hk_pos hk_lt
      interval_cases k <;> norm_num [pow_succ, ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact orderOf_eq_prime_of_pow_eq_one h1 h2
  have h_order_div : orderOf (2 : ZMod 23) ∣ 2 * n := by
    calc
      orderOf (2 : ZMod 23) ∣ 2 * n := by
        have : (2 : ZMod 23) ^ (2 * n) = 1 := by
          calc
            (2 : ZMod 23) ^ (2 * n) = ((2 : ZMod 23) ^ n) ^ 2 := by ring_nf
            _ = (-1 : ZMod 23) ^ 2 := by rw [h_mod]
            _ = 1 := by norm_num
        apply pow_orderOf_eq_one_iff.mp
        exact this
      _ = 2 * n := rfl
  have h_11_div_2n : 11 ∣ 2 * n := by
    rw [h_order_val] at h_order_div
    exact h_order_div
  have h_11_div_n : 11 ∣ n := by
    have : Nat.Coprime 11 2 := by decide
    exact Nat.Coprime.dvd_of_dvd_mul_left this h_11_div_2n
  have h_mod_1 : (2 : ZMod 23) ^ n = 1 := by
    have : orderOf (2 : ZMod 23) ∣ n := by
      rw [h_order_val]
      exact h_11_div_n
    apply pow_orderOf_eq_one
  rw [h_mod_1] at h_mod
  norm_num at h_mod
  contradiction
