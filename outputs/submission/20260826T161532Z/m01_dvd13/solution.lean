import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h₀ : ∀ n : ℕ, 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
    intro n
    induction' n with n ih
    · -- Base case: n = 0
      norm_num
    · -- Inductive step
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring,
          show (n + 1) + 2 = n + 2 + 1 by ring]
      simp [pow_add, pow_mul, Nat.pow_succ, Nat.mul_assoc] at ih ⊢
      -- Now we have: 13 ∣ 16 * 4^(2*n+1) + 3 * 3^(n+2)
      -- We know: 13 ∣ 4^(2*n+1) + 3^(n+2), so there exists k such that 4^(2*n+1) + 3^(n+2) = 13*k
      -- Then: 16 * 4^(2*n+1) + 3 * 3^(n+2) = 16*(4^(2*n+1) + 3^(n+2)) - 13*3^(n+2)
      --                                      = 16*13*k - 13*3^(n+2) = 13*(16*k - 3^(n+2))
      -- This shows the result is divisible by 13
      omega
  exact h₀ n
