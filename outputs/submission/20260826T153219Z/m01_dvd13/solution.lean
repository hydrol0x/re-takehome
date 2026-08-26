import Mathlib.Tactic

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
    -- Base case: n = 0
    norm_num [pow_succ, pow_zero]
    <;> decide
  | succ n ih =>
    -- Inductive step: assume for n, prove for n + 1
    rw [show 4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2) = 
          16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) by
      calc
        4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2) = 4 ^ (2 * n + 2 + 1) + 3 ^ (n + 1 + 2) := by ring_nf
        _ = 4 ^ (2 * n + 1 + 2) + 3 ^ (n + 2 + 1) := by ring_nf
        _ = 4 ^ (2 * n + 1) * 4 ^ 2 + 3 ^ (n + 2) * 3 ^ 1 := by
          rw [← pow_add, ← pow_add]
          <;> ring_nf
        _ = 4 ^ (2 * n + 1) * 16 + 3 ^ (n + 2) * 3 := by norm_num
        _ = 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by ring]
    
    -- Show that if 13 divides the sum, it also divides the next term
    have h₁ : 13 ∣ 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by
      have h₂ : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := ih
      -- Use the fact that 16 ≡ 3 (mod 13) to rewrite
      have h₃ : 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) = 
                 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) + 13 * 4 ^ (2 * n + 1) := by
        ring_nf
        <;> norm_num
        <;> omega
      
      rw [h₃]
      
      -- Both parts are divisible by 13
      have h₄ : 13 ∣ 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) := by
        exact dvd_mul_of_dvd_right h₂ 3
      
      have h₅ : 13 ∣ 13 * 4 ^ (2 * n + 1) := by
        exact dvd_mul_right _ _
      
      exact dvd_add h₄ h₅
    
    exact h₁
