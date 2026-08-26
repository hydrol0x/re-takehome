import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h : ∀ n : ℕ, 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0
      norm_num [Nat.dvd_iff_mod_eq_zero]
    | succ n ih =>
      -- Inductive step
      simp [pow_add, pow_mul, mul_add, add_mul, Nat.mul_succ] at ih ⊢
      -- Use omega to finish the divisibility check
      omega
  exact h n
