import Mathlib.Tactic

/-- A positive integer `n` satisfies `(n + 2) ∣ n ^ 2 + 4` iff `n = 2` or `n = 6`. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · -- Forward direction: assume (n + 2) ∣ n ^ 2 + 4
    intro h
    have h1 : (n + 2) ∣ (n + 2) ^ 2 := dvd_pow_self _ (by norm_num)
    have h2 : (n + 2) ∣ n ^ 2 + 4 * n + 4 := by
      rw [pow_two]
      ring_nf
      exact h1
    have h3 : (n + 2) ∣ 4 * n := by
      have h4 : (n + 2) ∣ (n ^ 2 + 4 * n + 4) - (n ^ 2 + 4) := Nat.dvd_sub' h2 h
      rw [show (n ^ 2 + 4 * n + 4) - (n ^ 2 + 4) = 4 * n by ring] at h4
      exact h4
    have h5 : (n + 2) ∣ 8 := by
      have h6 : (n + 2) ∣ 4 * (n + 2) := dvd_mul_right _ _
      have h7 : (n + 2) ∣ 4 * (n + 2) - 4 * n := Nat.dvd_sub' h6 h3
      rw [show 4 * (n + 2) - 4 * n = 8 by ring] at h7
      exact h7
    have h8 : n + 2 ≤ 8 := Nat.le_of_dvd (by norm_num) h5
    have h9 : n ≤ 6 := by omega
    have h10 : n = 2 ∨ n = 6 := by
      have h11 : n ≥ 1 := hn
      interval_cases n <;> simp_all (config := {decide := true})
    exact h10
  · -- Backward direction: check n = 2 and n = 6
    rintro (rfl | rfl)
    · norm_num
    · norm_num
