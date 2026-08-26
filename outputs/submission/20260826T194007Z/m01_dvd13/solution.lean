import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h : ∀ k : ℕ, 13 ∣ 4 ^ (2 * k + 1) + 3 ^ (k + 2) := by
    intro k
    induction' k with k ih
    · -- Base case: n = 0
      norm_num [Nat.dvd_iff_mod_eq_zero]
    · -- Inductive step
      simp_all [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.add_mod]
      <;> omega
  exact h n
