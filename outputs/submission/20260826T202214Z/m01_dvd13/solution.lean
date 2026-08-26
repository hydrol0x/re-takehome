import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h_main : ∀ k : ℕ, 13 ∣ 4 ^ (2 * k + 1) + 3 ^ (k + 2) := by
    intro k
    induction' k with k ih
    · -- Base case: k = 0
      norm_num [Nat.dvd_iff_mod_eq_zero]
    · -- Inductive step
      rw [show (2 * (k + 1) + 1 : ℕ) = 2 * k + 3 by ring]
      rw [show ((k + 1) + 2 : ℕ) = k + 3 by ring]
      have h1 : 4 ^ (2 * k + 3) + 3 ^ (k + 3) = 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) := by
        calc
          4 ^ (2 * k + 3) + 3 ^ (k + 3) = 4 ^ (2 * k + 1 + 2) + 3 ^ (k + 2 + 1) := by ring_nf
          _ = 4 ^ (2 * k + 1) * 4 ^ 2 + 3 ^ (k + 2) * 3 ^ 1 := by
            rw [pow_add, pow_add]
            <;> ring_nf
          _ = 4 ^ (2 * k + 1) * 16 + 3 ^ (k + 2) * 3 := by norm_num
          _ = 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) := by ring
      rw [h1]
      -- From IH: 13 ∣ 4^(2k+1) + 3^(k+2), so 4^(2k+1) ≡ -3^(k+2) (mod 13)
      -- We need 13 ∣ 16·4^(2k+1) + 3·3^(k+2)
      -- Note: 16 ≡ 3 (mod 13), so 16·4^(2k+1) + 3·3^(k+2) ≡ 3·4^(2k+1) + 3·3^(k+2) = 3(4^(2k+1) + 3^(k+2)) (mod 13)
      have h2 : 13 ∣ 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) := by
        -- Use the fact that 16 ≡ 3 (mod 13)
        have h3 : 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) = 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) + 13 * 4 ^ (2 * k + 1) := by
          ring_nf
          <;> simp [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
          <;> ring_nf
          <;> omega
        rw [h3]
        -- Both terms are divisible by 13
        exact dvd_add (by
          exact dvd_mul_of_dvd_right ih _) (by
            apply dvd_mul_right)
      exact h2
  exact h_main n
