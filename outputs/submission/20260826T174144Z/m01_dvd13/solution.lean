import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h_base : 13 ∣ 4 ^ (2 * 0 + 1) + 3 ^ (0 + 2) := by
    norm_num [Nat.dvd_iff_mod_eq_zero]
  
  have h_step (k : ℕ) (h : 13 ∣ 4 ^ (2 * k + 1) + 3 ^ (k + 2)) : 
    13 ∣ 4 ^ (2 * (k + 1) + 1) + 3 ^ ((k + 1) + 2) := by
    have h1 : 4 ^ (2 * (k + 1) + 1) + 3 ^ ((k + 1) + 2) = 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) := by
      ring_nf
      <;> simp [pow_add, pow_mul, mul_assoc, mul_comm, mul_left_comm]
      <;> ring_nf
    rw [h1]
    have h2 : 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) = 13 * 4 ^ (2 * k + 1) + 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) := by
      ring
    rw [h2]
    exact dvd_add (dvd_mul_right _ _) (by
      obtain ⟨m, hm⟩ := h
      use 3 * m
      rw [hm]
      ring)
  
  induction n with
  | zero => exact h_base
  | succ n ih => exact h_step n ih
