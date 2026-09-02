import Mathlib.Tactic

/-- A positive integer `n` satisfies `(n + 2) ∣ n ^ 2 + 4` iff `n = 2` or `n = 6`. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · -- Forward direction: (n + 2) ∣ n ^ 2 + 4 → n = 2 ∨ n = 6
    intro h
    have h_sq : (n + 2) ∣ (n + 2) ^ 2 := dvd_pow_self _ (by norm_num)
    have h_diff : (n + 2) ∣ (n + 2) ^ 2 - (n ^ 2 + 4) := dvd_sub h_sq h
    have h_4n : (n + 2) ∣ 4 * n := by
      rw [show (n + 2) ^ 2 - (n ^ 2 + 4) = 4 * n by ring] at h_diff
      exact h_diff
    have h_4n_plus_8 : (n + 2) ∣ 4 * (n + 2) := dvd_mul_right _ _
    have h_8 : (n + 2) ∣ 4 * (n + 2) - 4 * n := dvd_sub h_4n_plus_8 h_4n
    have h_8_val : 4 * (n + 2) - 4 * n = 8 := by ring
    rw [h_8_val] at h_8
    have h_bound : n ≤ 6 := by
      have h_le : n + 2 ≤ 8 := Nat.le_of_dvd (by norm_num) h_8
      omega
    interval_cases n <;> norm_num at h_8 ⊢ <;> try contradiction <;> omega
  · -- Backward direction: n = 2 ∨ n = 6 → (n + 2) ∣ n ^ 2 + 4
    rintro (rfl | rfl)
    · -- Case n = 2
      norm_num
    · -- Case n = 6
      norm_num
