import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
    norm_num [Nat.dvd_iff_mod_eq_zero]
  | succ n ih =>
    have h₁ : 4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2) = 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by
      simp [pow_add, pow_mul, Nat.mul_assoc]
      ring_nf
      <;> simp_all [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
      <;> ring_nf
    rw [h₁]
    have h₂ : 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) = 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) + 13 * 4 ^ (2 * n + 1) := by
      ring_nf
    rw [h₂]
    apply dvd_add
    · -- Show 13 divides 3 * (4^(2*n+1) + 3^(n+2))
      apply dvd_mul_of_dvd_right
      exact ih
    · -- Show 13 divides 13 * 4^(2*n+1)
      apply dvd_mul_right
