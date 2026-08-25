import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h_base : 13 ∣ 4 ^ (2 * 0 + 1) + 3 ^ (0 + 2) := by
    norm_num [Nat.dvd_iff_mod_eq_zero]
  
  have h_induction : ∀ k : ℕ, 13 ∣ 4 ^ (2 * k + 1) + 3 ^ (k + 2) → 13 ∣ 4 ^ (2 * (k + 1) + 1) + 3 ^ ((k + 1) + 2) := by
    intro k hk
    rw [show 4 ^ (2 * (k + 1) + 1) + 3 ^ ((k + 1) + 2) = 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) by
      ring_nf]
    
    -- Use the fact that 16 ≡ 3 (mod 13), so 16 * a + 3 * b ≡ 3 * a + 3 * b = 3(a + b) (mod 13)
    -- Since 13 | (a + b), we have 13 | 3(a + b)
    have h₁ : 13 ∣ 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) := by
      exact dvd_mul_of_dvd_right hk 3
    
    have h₂ : 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) = 13 * 4 ^ (2 * k + 1) + 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) := by
      ring
    
    rw [h₂]
    
    -- Show both terms are divisible by 13
    apply dvd_add
    · -- First term: 13 * 4^(2k+1) is clearly divisible by 13
      exact ⟨4 ^ (2 * k + 1), by ring⟩
    · -- Second term: 3 * (4^(2k+1) + 3^(k+2)) is divisible by 13 by h₃
      exact h₁
  
  induction n with
  | zero => exact h_base
  | succ k ih => exact h_induction k ih
