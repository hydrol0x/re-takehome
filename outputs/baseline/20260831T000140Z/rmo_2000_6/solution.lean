import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

open Nat

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 20) := by
  constructor
  · -- first part: the least possible value of `ab` is `10`
    refine ⟨?_, ?_⟩
    · -- `10` belongs to the set
      refine ⟨1, 10, ?_, ?_, ?_, rfl⟩
      all_goals decide
    · -- any element of the set is at least `10`
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ^ 4 ∣ a ^ 2 * b ^ 5 := by
        have : (2 ^ 4 * 5 ^ 3) ∣ a ^ 2 * b ^ 5 := hdiv
        exact dvd_trans this (dvd_mul_left _ _)
      have h5 : 5 ^ 3 ∣ a ^ 2 * b ^ 5 := by
        have : (2 ^ 4 * 5 ^ 3) ∣ a ^ 2 * b ^ 5 := hdiv
        exact dvd_trans this (dvd_mul_right _ _)
      have h2a : 2 ^ 2 ∣ a ^ 2 ∨ 2 ^ 2 ∣ b ^ 5 := by
        have : 2 ^ 4 ∣ a ^ 2 * b ^ 5 := h2
        exact dvd_mul_of_dvd_left (pow_dvd_pow (Nat.succ_le_of_lt (by decide)) _) _
      have h5a : 5 ^ 2 ∣ a ^ 2 ∨ 5 ^ 2 ∣ b ^ 5 := by
        have : 5 ^ 3 ∣ a ^ 2 * b ^ 5 := h5
        exact dvd_mul_of_dvd_left (pow_dvd_pow (Nat.succ_le_of_lt (by decide)) _) _
      have h2ab : 2 ∣ a * b := by
        rcases h2a with h2a | h2a
        · exact dvd_trans (dvd_pow_self _ (by decide)) (dvd_mul_of_dvd_left h2a _)
        · exact dvd_trans (dvd_pow_self _ (by decide)) (dvd_mul_of_dvd_right h2a _)
      have h5ab : 5 ∣ a * b := by
        rcases h5a with h5a | h5a
        · exact dvd_trans (dvd_pow_self _ (by decide)) (dvd_mul_of_dvd_left h5a _)
        · exact dvd_trans (dvd_pow_self _ (by decide)) (dvd_mul_of_dvd_right h5a _)
      have : 10 ∣ a * b := dvd_mul_of_dvd_left h2ab _
      exact Nat.le_of_dvd (Nat.succ_pos _) this
  · -- second part: the least possible value of `ab` is `20`
    refine ⟨?_, ?_⟩
    · -- `20` belongs to the set
      refine ⟨2, 10, ?_, ?_, ?_, rfl⟩
      all_goals decide
    · -- any element of the set is at least `20`
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ^ 4 ∣ a ^ 3 * b ^ 4 := by
        have : (2 ^ 4 * 5 ^ 3) ∣ a ^ 3 * b ^ 4 := hdiv
        exact dvd_trans this (dvd_mul_left _ _)
      have h5 : 5 ^ 3 ∣ a ^ 3 * b ^ 4 := by
        have : (2 ^ 4 * 5 ^ 3) ∣ a ^ 3 * b ^ 4 := hdiv
        exact dvd_trans this (dvd_mul_right _ _)
      have h2a : 2 ^ 3 ∣ a ^ 3 ∨ 2 ^ 3 ∣ b ^ 4 := by
        have : 2 ^ 4 ∣ a ^ 3 * b ^ 4 := h2
        exact dvd_mul_of_dvd_left (pow_dvd_pow (Nat.succ_le_of_lt (by decide)) _) _
      have h5a : 5 ^ 3 ∣ a ^ 3 ∨ 5 ^ 3 ∣ b ^ 4 := by
        have : 5 ^ 3 ∣ a ^ 3 * b ^ 4 := h5
        exact dvd_mul_of_dvd_left (pow_dvd_pow (Nat.succ_le_of_lt (by decide)) _) _
      have h2ab : 2 ∣ a * b := by
        rcases h2a with h2a | h2a
        · exact dvd_trans (dvd_pow_self _ (by decide)) (dvd_mul_of_dvd_left h2a _)
        · exact dvd_trans (dvd_pow_self _ (by decide)) (dvd_mul_of_dvd_right h2a _)
      have h5ab : 5 ∣ a * b := by
        rcases h5a with h5a | h5a
        · exact dvd_trans (dvd_pow_self _ (by decide)) (dvd_mul_of_dvd_left h5a _)
        · exact dvd_trans (dvd_pow_self _ (by decide)) (dvd_mul_of_dvd_right h5a _)
      have : 10 ∣ a * b := dvd_mul_of_dvd_left h2ab _
      have h2b : 2 ∣ a * b := by
        rcases h2a with h2a | h2a
        · exact dvd_trans (dvd_pow_self _ (by decide)) (dvd_mul_of_dvd_left h2a _)
        · exact dvd_trans (dvd_pow_self _ (by decide)) (dvd_mul_of_dvd_right h2a _)
      have : 20 ∣ a * b := dvd_mul_of_dvd_left h2b _
      exact Nat.le_of_dvd (Nat.succ_pos _) this
