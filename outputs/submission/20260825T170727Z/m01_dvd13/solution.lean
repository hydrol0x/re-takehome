import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h_main : ∀ n : ℕ, 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0
      norm_num [Nat.dvd_iff_mod_eq_zero]
    | succ n ih =>
      -- Inductive step: assume true for n, prove for n+1
      simp [pow_add, pow_mul, Nat.pow_succ, mul_assoc, mul_comm, mul_left_comm] at ih ⊢
      -- Use omega to finish the divisibility argument
      omega
  exact h_main n
