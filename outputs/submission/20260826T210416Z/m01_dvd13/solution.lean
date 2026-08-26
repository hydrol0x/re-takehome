import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h_main : ∀ n : ℕ, 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
    intro n
    induction' n with n ih
    · -- Base case: n = 0
      norm_num
    · -- Inductive step: assume true for n, prove for n + 1
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at ih ⊢
      norm_num at ih ⊢
      <;> omega
  exact h_main n
