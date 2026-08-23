import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

lemma factors_2000 : 2000 = 2 ^ 4 * 5 ^ 3 := by norm_num

lemma witness_10 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ 10 = a * b := by
  refine ⟨1, 10, by norm_num, by norm_num, by norm_num, rfl⟩

lemma witness_20 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ 20 = a * b := by
  refine ⟨1, 20, by norm_num, by norm_num, by norm_num, rfl⟩

lemma min_10_deferred : ∀ n : ℕ, (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b) → 10 ≤ n := by
  intro n h
  rcases h with ⟨a, b, ha, hb, hdiv, hn⟩
  by_contra h_not_ge
  push_neg at h_not_ge
  have h_ab : a * b < 10 := by rw [hn] at *; exact h_not_ge
  have ha : a < 10 := by nlinarith [hb]
  have hb' : b < 10 := by nlinarith [ha]
  interval_cases a <;> interval_cases b <;>
    (try omega) <;>
    (try norm_num [Nat.dvd_iff_mod_eq_zero] at hdiv)

lemma min_20_deferred : ∀ n : ℕ, (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b) → 20 ≤ n := by
  sorry

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 20) := by
  constructor
  · constructor
    · exact witness_10
    · exact min_10_deferred
  · constructor
    · exact witness_20
    · exact min_20_deferred
