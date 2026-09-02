import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
    -- Base case: n = 0
    -- 4^(2*0+1) + 3^(0+2) = 4^1 + 3^2 = 4 + 9 = 13
    norm_num [Nat.dvd_iff_mod_eq_zero]
  | succ n ih =>
    -- Inductive step: assume the statement holds for n, prove for n+1
    -- We need to show: 13 ∣ 4^(2*(n+1)+1) + 3^((n+1)+2)
    -- That is: 13 ∣ 4^(2*n+3) + 3^(n+3)
    -- Note: 4^(2*n+3) + 3^(n+3) = 16 * 4^(2*n+1) + 3 * 3^(n+2)
    --      = 13 * 4^(2*n+1) + 3 * (4^(2*n+1) + 3^(n+2))
    -- Since 13 ∣ 4^(2*n+1) + 3^(n+2) by IH, and 13 ∣ 13 * 4^(2*n+1),
    -- we have 13 ∣ 4^(2*n+3) + 3^(n+3)
    
    rw [show 4 ^ (2 * (n + 1) + 1) = 16 * 4 ^ (2 * n + 1) by
      ring_nf
      <;> simp [pow_add, pow_mul, mul_assoc]]
    rw [show 3 ^ ((n + 1) + 2) = 3 * 3 ^ (n + 2) by
      ring_nf
      <;> simp [pow_add, pow_succ, mul_assoc]]
    
    -- Now we have: 16 * 4^(2*n+1) + 3 * 3^(n+2)
    -- Rewrite as: 13 * 4^(2*n+1) + 3 * (4^(2*n+1) + 3^(n+2))
    have h₁ : 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) = 
      13 * 4 ^ (2 * n + 1) + 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) := by
      ring
    rw [h₁]
    
    -- Both terms are divisible by 13
    apply dvd_add
    · exact ⟨4 ^ (2 * n + 1), by ring⟩
    · -- Use the inductive hypothesis
      obtain ⟨k, hk⟩ := ih
      use 3 * k
      rw [hk]
      ring
