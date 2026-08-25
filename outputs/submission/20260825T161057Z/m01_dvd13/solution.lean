import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h_base : 13 ∣ 4 ^ (2 * 0 + 1) + 3 ^ (0 + 2) := by norm_num
  have h_ind : ∀ k : ℕ, 13 ∣ 4 ^ (2 * k + 1) + 3 ^ (k + 2) → 13 ∣ 4 ^ (2 * (k + 1) + 1) + 3 ^ ((k + 1) + 2) := by
    intro k hk
    have h1 : 4 ^ (2 * (k + 1) + 1) = 16 * 4 ^ (2 * k + 1) := by
      ring_nf
      <;> simp [pow_add, pow_mul]
      <;> ring_nf
    have h2 : 3 ^ ((k + 1) + 2) = 3 * 3 ^ (k + 2) := by
      ring_nf
      <;> simp [pow_add, pow_mul]
      <;> ring_nf
    rw [h1, h2]
    have h3 : 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) = 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) + 13 * 4 ^ (2 * k + 1) := by
      ring_nf
    rw [h3]
    have h4 : 13 ∣ 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) := dvd_mul_of_dvd_right hk _
    have h5 : 13 ∣ 13 * 4 ^ (2 * k + 1) := dvd_mul_right _ _
    exact dvd_add h4 h5
  induction' n with k ih
  · exact h_base
  · exact h_ind k ih
