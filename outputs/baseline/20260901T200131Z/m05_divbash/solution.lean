import Mathlib
import Mathlib.Tactic

theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · intro h
    have h_sq : n + 2 ∣ (n + 2) ^ 2 := by
      apply dvd_pow_self _ (by decide)
    rw [show (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 by ring] at h_sq
    
    have h_4n : n + 2 ∣ 4 * n := by
      have h_le : n ^ 2 + 4 ≤ n ^ 2 + 4 * n + 4 := by nlinarith
      exact Nat.dvd_sub' h_sq h h_le
      
    have h_4n_plus_8 : n + 2 ∣ 4 * n + 8 := by
      rw [show 4 * n + 8 = 4 * (n + 2) by ring]
      exact dvd_mul_right (n + 2) 4
      
    have h_8 : n + 2 ∣ 8 := by
      have h_le_8 : 4 * n ≤ 4 * n + 8 := by nlinarith
      exact Nat.dvd_sub' h_4n_plus_8 h_4n h_le_8
      
    have h_bound : n + 2 ≤ 8 := Nat.le_of_dvd (by decide) h_8
    have h_n_le_6 : n ≤ 6 := by omega
    
    interval_cases n <;> norm_num at h ⊢ <;> try contradiction
  · rintro (rfl | rfl)
    · norm_num
    · norm_num
