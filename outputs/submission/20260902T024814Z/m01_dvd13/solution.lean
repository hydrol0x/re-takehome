import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h_mod_13_pow_16 : 16 % 13 = 3 := by decide
  have h_mod_13_pow_3 : 3 % 13 = 3 := by decide
  
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 =>
    -- Base case: n = 0
    norm_num [Nat.dvd_iff_mod_eq_zero]
  | k + 1 =>
    -- Inductive step
    have h_k := ih k (by omega)
    
    -- We need to show 13 ∣ 4^(2*(k+1)+1) + 3^((k+1)+2)
    -- = 4^(2k+3) + 3^(k+3)
    -- = 16 * 4^(2k+1) + 3 * 3^(k+2)
    
    rw [show 4 ^ (2 * (k + 1) + 1) = 16 * 4 ^ (2 * k + 1) by
      {
        simp [pow_add, pow_mul, mul_comm]
        ring_nf
      },
      show 3 ^ ((k + 1) + 2) = 3 * 3 ^ (k + 2) by
      {
        simp [pow_add, add_assoc]
        ring_nf
      }]
    
    -- Use the fact that 16 ≡ 3 (mod 13)
    have h1 : 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) = 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) + 13 * 4 ^ (2 * k + 1) := by
      ring_nf
    
    rw [h1]
    
    -- Since 13 ∣ 4^(2k+1) + 3^(k+2) and 13 ∣ 13 * 4^(2k+1), we have 13 divides the sum
    have h2 : 13 ∣ 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) := by
      -- If 13 ∣ x then 13 ∣ 3*x
      exact dvd_mul_of_dvd_right h_k 3
    
    have h3 : 13 ∣ 13 * 4 ^ (2 * k + 1) := by
      -- 13 always divides 13 * anything
      exact ⟨4 ^ (2 * k + 1), by ring⟩
    
    -- Sum of two multiples of 13 is a multiple of 13
    exact dvd_add h2 h3
