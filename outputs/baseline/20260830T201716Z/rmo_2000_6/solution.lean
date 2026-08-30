import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Order.Bounds.Basic

open Nat

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- Part 1
    constructor
    · -- Existence
      use 1, 10
      simp [mul_comm]
      norm_num
    · -- Minimality
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ∣ a * b := by
        -- Prove 2 divides ab
        have h2_val : 4 ≤ multiplicity 2 (a ^ 2 * b ^ 5) := by
          rw [← dvd_iff_multiplicity_le]
          exact hdiv
        have h2_sum : 4 ≤ 2 * multiplicity 2 a + 5 * multiplicity 2 b := by
          simp [multiplicity.pow, multiplicity.mul] at h2_val
          exact h2_val
        -- Case analysis on multiplicity 2 b
        have h2_min : 1 ≤ multiplicity 2 a + multiplicity 2 b := by
          by_contra h
          have h' : multiplicity 2 a + multiplicity 2 b = 0 := by omega
          have h_a : multiplicity 2 a = 0 := by omega
          have h_b : multiplicity 2 b = 0 := by omega
          rw [h_a, h_b] at h2_sum
          norm_num at h2_sum
          contradiction
        exact dvd_of_multiplicity_pos h2_min
      have h5 : 5 ∣ a * b := by
        -- Similar for 5
        have h5_val : 3 ≤ multiplicity 5 (a ^ 2 * b ^ 5) := by
          rw [← dvd_iff_multiplicity_le]
          exact hdiv
        have h5_sum : 3 ≤ 2 * multiplicity 5 a + 5 * multiplicity 5 b := by
          simp [multiplicity.pow, multiplicity.mul] at h5_val
          exact h5_val
        have h5_min : 1 ≤ multiplicity 5 a + multiplicity 5 b := by
          by_contra h
          have h' : multiplicity 5 a + multiplicity 5 b = 0 := by omega
          have h_a : multiplicity 5 a = 0 := by omega
          have h_b : multiplicity 5 b = 0 := by omega
          rw [h_a, h_b] at h5_sum
          norm_num at h5_sum
          contradiction
        exact dvd_of_multiplicity_pos h5_min
      have h10 : 10 ∣ a * b := by
        apply dvd_trans _ (dvd_mul_of_dvd_left h2 _)
        exact dvd_mul_right 2 5
      omega
  · -- Part 2
    constructor
    · -- Existence
      use 1, 10
      simp [mul_comm]
      norm_num
    · -- Minimality
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ∣ a * b := by
        have h2_val : 4 ≤ multiplicity 2 (a ^ 3 * b ^ 4) := by
          rw [← dvd_iff_multiplicity_le]
          exact hdiv
        have h2_sum : 4 ≤ 3 * multiplicity 2 a + 4 * multiplicity 2 b := by
          simp [multiplicity.pow, multiplicity.mul] at h2_val
          exact h2_val
        have h2_min : 1 ≤ multiplicity 2 a + multiplicity 2 b := by
          by_contra h
          have h' : multiplicity 2 a + multiplicity 2 b = 0 := by omega
          have h_a : multiplicity 2 a = 0 := by omega
          have h_b : multiplicity 2 b = 0 := by omega
          rw [h_a, h_b] at h2_sum
          norm_num at h2_sum
          contradiction
        exact dvd_of_multiplicity_pos h2_min
      have h5 : 5 ∣ a * b := by
        have h5_val : 3 ≤ multiplicity 5 (a ^ 3 * b ^ 4) := by
          rw [← dvd_iff_multiplicity_le]
          exact hdiv
        have h5_sum : 3 ≤ 3 * multiplicity 5 a + 4 * multiplicity 5 b := by
          simp [multiplicity.pow, multiplicity.mul] at h5_val
          exact h5_val
        have h5_min : 1 ≤ multiplicity 5 a + multiplicity 5 b := by
          by_contra h
          have h' : multiplicity 5 a + multiplicity 5 b = 0 := by omega
          have h_a : multiplicity 5 a = 0 := by omega
          have h_b : multiplicity 5 b = 0 := by omega
          rw [h_a, h_b] at h5_sum
          norm_num at h5_sum
          contradiction
        exact dvd_of_multiplicity_pos h5_min
      have h10 : 10 ∣ a * b := by
        apply dvd_trans _ (dvd_mul_of_dvd_left h2 _)
        exact dvd_mul_right 2 5
      omega
