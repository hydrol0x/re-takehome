import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
    norm_num [Nat.dvd_iff_mod_eq_zero]
  | succ k ih =>
    rw [show 4 ^ (2 * (k + 1) + 1) + 3 ^ ((k + 1) + 2) = 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) by
      calc
        4 ^ (2 * (k + 1) + 1) + 3 ^ ((k + 1) + 2) = 4 ^ (2 * k + 2 + 1) + 3 ^ (k + 1 + 2) := by ring
        _ = 4 ^ (2 * k + 3) + 3 ^ (k + 3) := by ring
        _ = 4 ^ (2 * k + 1 + 2) + 3 ^ (k + 2 + 1) := by ring
        _ = 4 ^ 2 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) := by
          rw [pow_add, pow_add]
          <;> ring
        _ = 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) := by norm_num]
    -- We have 16 * 4^(2k+1) + 3 * 3^(k+2)
    -- From IH: 13 ∣ 4^(2k+1) + 3^(k+2), so 4^(2k+1) + 3^(k+2) = 13 * m for some m
    -- 16 * 4^(2k+1) + 3 * 3^(k+2) = 16 * 4^(2k+1) + 3 * 3^(k+2) - 13 * 3^(k+2) + 13 * 3^(k+2)
    -- = 16 * 4^(2k+1) - 10 * 3^(k+2) + 13 * 3^(k+2)
    -- = 16 * 4^(2k+1) - 10 * 3^(k+2) + 13 * 3^(k+2)
    -- Actually, let's rewrite: 16 * 4^(2k+1) + 3 * 3^(k+2) = 16 * 4^(2k+1) + 3 * 3^(k+2) - 13 * 4^(2k+1) + 13 * 4^(2k+1)
    -- = 3 * 4^(2k+1) + 3 * 3^(k+2) + 13 * 4^(2k+1)
    -- = 3 * (4^(2k+1) + 3^(k+2)) + 13 * 4^(2k+1)
    -- Both terms are divisible by 13
    
    have h₁ : 13 ∣ 4 ^ (2 * k + 1) + 3 ^ (k + 2) := ih
    have h₂ : 13 ∣ 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) := dvd_mul_of_dvd_right h₁ 3
    have h₃ : 13 ∣ 13 * 4 ^ (2 * k + 1) := by
      apply dvd_mul_right
    have h₄ : 13 ∣ 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) + 13 * 4 ^ (2 * k + 1) := dvd_add h₂ h₃
    have h₅ : 3 * (4 ^ (2 * k + 1) + 3 ^ (k + 2)) + 13 * 4 ^ (2 * k + 1) = 16 * 4 ^ (2 * k + 1) + 3 * 3 ^ (k + 2) := by
      ring
    rw [h₅] at h₄
    exact h₄
