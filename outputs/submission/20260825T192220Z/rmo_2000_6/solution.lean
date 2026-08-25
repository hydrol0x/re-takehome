import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

-- Helper lemmas for part 1
theorem rmo_2000_6_part1_exists : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ a * b = 10 := by
  exact ⟨1, 10, by decide, by decide, by norm_num [pow_succ], by decide⟩

theorem rmo_2000_6_part1_minimal : ∀ n : ℕ, (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b) → 10 ≤ n := by
  intro n h
  rcases h with ⟨a, b, ha, hb, hdvd, hn⟩
  rw [hn]
  have h₁ : 2000 ∣ a ^ 2 * b ^ 5 := hdvd
  have h₂ : a * b = n := hn.symm
  have h₃ : 0 < a := ha
  have h₄ : 0 < b := hb
  by_contra h
  push_neg at h
  have h₅ : a * b ≤ 9 := by linarith
  -- Candidate 1: Direct case analysis with omega
  have h₆ : a ≤ 9 := by
    nlinarith [h₅]
  have h₇ : b ≤ 9 := by
    nlinarith [h₅]
  interval_cases a <;>
    interval_cases b <;>
    (try omega) <;>
    (try norm_num [Nat.dvd_iff_mod_eq_zero] at h₁ <;> omega)

-- Helper lemmas for part 2
theorem rmo_2000_6_part2_exists : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ a * b = 20 := by
  exact ⟨1, 20, by decide, by decide, by norm_num [pow_succ], by decide⟩

theorem rmo_2000_6_part2_minimal : ∀ n : ℕ, (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b) → 20 ≤ n := by
  intro n h
  rcases h with ⟨a, b, ha, hb, hdvd, hn⟩
  rw [hn]
  by_contra h
  push_neg at h
  have h₁ : a * b ≤ 19 := by omega
  sorry

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 20) := by
  sorry
