import Mathlib
import Mathlib.Tactic

theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · intro h
    have h_sq : n + 2 ∣ (n + 2) ^ 2 := by
      apply dvd_mul_right
    have h_sq_expanded : (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 := by ring
    rw [h_sq_expanded] at h_sq
    have h_4n : n + 2 ∣ 4 * n := by
      have h_le : n ^ 2 + 4 ≤ n ^ 2 + 4 * n + 4 := by
        have : 0 ≤ 4 * n := by positivity
        omega
      exact Nat.dvd_sub' h_sq h
    have h_4n_plus_8 : n + 2 ∣ 4 * (n + 2) := by
      apply dvd_mul_right
    have h_8 : n + 2 ∣ 8 := by
      have h_eq : 4 * (n + 2) = 4 * n + 8 := by ring
      rw [h_eq] at h_4n_plus_8
      have h_le2 : 4 * n ≤ 4 * n + 8 := by omega
      exact Nat.dvd_sub' h_4n_plus_8 h_4n
    have h_upper : n + 2 ≤ 8 := Nat.le_of_dvd (by decide) h_8
    have h_lower : 3 ≤ n + 2 := by omega
    interval_cases n + 2 <;> omega
  · rintro (rfl | rfl) <;> norm_num
