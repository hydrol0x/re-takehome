import Mathlib

theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · -- Forward direction: (n + 2) ∣ n ^ 2 + 4 → n = 2 ∨ n = 6
    intro h
    -- (n + 2) divides (n + 2)^2
    have h_sq : (n + 2) ∣ (n + 2) * (n + 2) := dvd_mul_right (n + 2) (n + 2)
    -- Expand (n + 2)^2 to n^2 + 4n + 4
    have h_expand : (n + 2) * (n + 2) = n ^ 2 + 4 * n + 4 := by ring
    -- Therefore (n + 2) divides n^2 + 4n + 4
    have h_poly : (n + 2) ∣ n ^ 2 + 4 * n + 4 := by
      rw [← h_expand]
      exact h_sq
    -- We have (n + 2) ∣ n^2 + 4 and (n + 2) ∣ n^2 + 4n + 4
    -- Their difference is 4n.
    have h_le_1 : n ^ 2 + 4 ≤ n ^ 2 + 4 * n + 4 := by nlinarith
    have h_4n : (n + 2) ∣ 4 * n := by
      apply Nat.dvd_sub h_poly h h_le_1
    -- (n + 2) divides 4(n + 2) = 4n + 8
    have h_4n_plus_8 : (n + 2) ∣ 4 * (n + 2) := by rw [mul_comm]; exact dvd_mul_right (n + 2) 4
    -- Their difference is 8.
    have h_le_2 : 4 * n ≤ 4 * (n + 2) := by nlinarith
    have h_8 : (n + 2) ∣ 8 := by
      apply Nat.dvd_sub h_4n_plus_8 h_4n h_le_2
    -- Since (n + 2) ∣ 8 and n > 0, n + 2 must be a divisor of 8 greater than 2.
    -- Divisors of 8 are 1, 2, 4, 8. Since n > 0, n + 2 ≥ 3.
    -- So n + 2 ∈ {4, 8}.
    have h_n_bound : n + 2 ≤ 8 := Nat.le_of_dvd (by norm_num) h_8
    have h_n_le_6 : n ≤ 6 := by omega
    -- Check each possible value of n from 1 to 6
    interval_cases n <;> norm_num at h_8 hn ⊢ <;> try omega
  · -- Backward direction: n = 2 ∨ n = 6 → (n + 2) ∣ n ^ 2 + 4
    rintro (rfl | rfl)
    · -- Case n = 2
      norm_num
    · -- Case n = 6
      norm_num
