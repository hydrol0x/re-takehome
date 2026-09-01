import Mathlib

theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · -- Forward direction
    intro h
    have h1 : (n + 2) ∣ (n + 2) ^ 2 := dvd_mul_right _ _
    have h2 : n ^ 2 + 4 ≤ (n + 2) ^ 2 := by
      have : 0 ≤ 4 * n := by positivity
      omega
    have h3 : (n + 2) ∣ (n + 2) ^ 2 - (n ^ 2 + 4) := Nat.dvd_sub' h1 h h2
    have h4 : (n + 2) ^ 2 - (n ^ 2 + 4) = 4 * n := by
      rw [pow_two, pow_two]
      simp [add_assoc, add_comm, add_left_comm, mul_add, mul_comm, mul_left_comm]
      <;> omega
    rw [h4] at h3
    have h5 : (n + 2) ∣ 4 * (n + 2) := dvd_mul_right _ _
    have h6 : 4 * n ≤ 4 * (n + 2) := by
      have : n ≤ n + 2 := by omega
      exact Nat.mul_le_mul_left 4 this
    have h7 : (n + 2) ∣ 4 * (n + 2) - 4 * n := Nat.dvd_sub' h5 h3 h6
    have h8 : 4 * (n + 2) - 4 * n = 8 := by
      rw [mul_add, mul_comm, mul_left_comm, mul_assoc]
      simp [add_assoc, add_comm, add_left_comm]
      <;> omega
    rw [h8] at h7
    have h9 : n + 2 ≤ 8 := Nat.le_of_dvd (by decide) h7
    have h10 : n ≤ 6 := by omega
    have h11 : n = 2 ∨ n = 6 := by
      interval_cases n <;> norm_num at h3 ⊢ <;> try { contradiction } <;> try { tauto }
    exact h11
  · -- Backward direction
    rintro (rfl | rfl) <;> norm_num
