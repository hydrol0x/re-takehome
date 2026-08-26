import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h : ∀ n : ℕ, 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0
      -- 4^1 + 3^2 = 4 + 9 = 13, which is divisible by 13
      norm_num
    | succ n ih =>
      -- Inductive step: assume true for n, prove for n+1
      -- 4^(2(n+1)+1) + 3^((n+1)+2) = 4^(2n+3) + 3^(n+3)
      --                           = 16 * 4^(2n+1) + 3 * 3^(n+2)
      -- We know 13 ∣ 4^(2n+1) + 3^(n+2), so we write:
      -- 16 * 4^(2n+1) + 3 * 3^(n+2) = 13 * 4^(2n+1) + 3 * (4^(2n+1) + 3^(n+2))
      -- Since both terms are divisible by 13, their sum is divisible by 13
      
      have h₁ : 4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2) = 
                16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by
        ring_nf
        <;> simp [pow_add, pow_mul, mul_assoc]
        <;> ring_nf
      
      rw [h₁]
      
      -- Rewrite as: 16 * 4^(2n+1) + 3 * 3^(n+2) = 13 * 4^(2n+1) + 3 * (4^(2n+1) + 3^(n+2))
      have h₂ : 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) = 
                13 * 4 ^ (2 * n + 1) + 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) := by
        ring_nf
      
      rw [h₂]
      
      -- Both terms are divisible by 13
      -- First term: 13 * 4^(2n+1) is clearly divisible by 13
      -- Second term: 3 * (4^(2n+1) + 3^(n+2)) is divisible by 13 by IH
      exact dvd_add (dvd_mul_right 13 _) (dvd_mul_of_dvd_right ih _)
  
  exact h n
