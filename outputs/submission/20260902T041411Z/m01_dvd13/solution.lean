import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h : ∀ k : ℕ, 13 ∣ 4 ^ (2 * k + 1) + 3 ^ (k + 2) := by
    intro k
    induction k with
    | zero =>
      -- Base case: k = 0
      norm_num [Nat.dvd_iff_mod_eq_zero]
    | succ k ih =>
      -- Inductive step
      have h₁ : 4 ^ (2 * (k + 1) + 1) + 3 ^ ((k + 1) + 2) = 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) := by
        ring_nf
        <;> simp [pow_add, pow_mul, mul_add, add_mul]
        <;> ring_nf
      rw [h₁]
      have h₂ : 13 ∣ 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) := by
        -- Use the inductive hypothesis that 13 divides 4^(2k+1) + 3^(k+2)
        have h₃ : 13 ∣ 4 ^ (2 * k + 1) + 3 ^ (k + 2) := ih
        -- Rewrite as: 16 * A + 3 * B where A + B is divisible by 13
        -- Note: 16 * A + 3 * B = 13 * A + 3 * (A + B)
        have h₄ : 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) = 13 * 4 ^ (2 * k + 1) + 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) := by
          ring
        rw [h₄]
        exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right h₃ _)
      exact h₂
  exact h n
