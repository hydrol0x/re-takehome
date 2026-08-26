import Mathlib.Tactic
import Mathlib.Data.Nat.Digits

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h : ∀ n : ℕ, 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0
      -- 4^(2*0+1) + 3^(0+2) = 4^1 + 3^2 = 4 + 9 = 13
      norm_num [Nat.dvd_iff_mod_eq_zero]
    | succ k ih =>
      -- Inductive step: assume for k, prove for k+1
      -- 4^(2*(k+1)+1) + 3^((k+1)+2) = 4^(2k+3) + 3^(k+3)
      -- = 16 * 4^(2k+1) + 3 * 3^(k+2)
      -- We know 13 ∣ 4^(2k+1) + 3^(k+2), so we want to show 13 ∣ 16 * 4^(2k+1) + 3 * 3^(k+2)
      -- Note: 16 ≡ 3 (mod 13), so 16 * 4^(2k+1) + 3 * 3^(k+2) ≡ 3 * 4^(2k+1) + 3 * 3^(k+2) (mod 13)
      -- ≡ 3 * (4^(2k+1) + 3^(k+2)) (mod 13)
      -- Since 13 ∣ 4^(2k+1) + 3^(k+2), we have 13 ∣ 3 * (4^(2k+1) + 3^(k+2))
      
      have h₁ : 4 ^ (2 * (k + 1) + 1) + 3 ^ ((k + 1) + 2) = 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) := by
        ring_nf
        <;> simp [pow_add, pow_mul, mul_assoc]
        <;> ring_nf
      
      rw [h₁]
      -- Use the fact that 13 divides the original expression
      -- 16 * 4^(2k+1) + 3 * 3^(k+2) = 13 * 4^(2k+1) + 3 * 4^(2k+1) + 3 * 3^(k+2)
      -- = 13 * 4^(2k+1) + 3 * (4^(2k+1) + 3^(k+2))
      -- Both terms are divisible by 13
      
      have h₂ : 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) = 13 * 4 ^ (2 * k + 1) + 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) := by
        ring
      
      rw [h₂]
      -- Now we can use dvd_add
      apply dvd_add
      · -- 13 ∣ 13 * 4^(2k+1)
        exact ⟨4 ^ (2 * k + 1), by ring⟩
      · -- 13 ∣ 3 * (4^(2k+1) + 3^(k+2))
        -- Since 13 ∣ 4^(2k+1) + 3^(k+2) by IH
        obtain ⟨m, hm⟩ := ih
        use 3 * m
        rw [hm]
        ring
  exact h n
