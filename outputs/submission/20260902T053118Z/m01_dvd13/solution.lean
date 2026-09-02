import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    have h_pow_4 : 4 ^ (2 * (n + 1) + 1) = 16 * 4 ^ (2 * n + 1) := by
      calc
        4 ^ (2 * (n + 1) + 1) = 4 ^ (2 * n + 3) := by
          rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
        _ = 4 ^ (2 * n + 1 + 2) := by
          rw [show 2 * n + 3 = 2 * n + 1 + 2 by ring]
        _ = 4 ^ (2 * n + 1) * 4 ^ 2 := by rw [pow_add]
        _ = 4 ^ (2 * n + 1) * 16 := by norm_num
        _ = 16 * 4 ^ (2 * n + 1) := by ring
    have h_pow_3 : 3 ^ ((n + 1) + 2) = 3 * 3 ^ (n + 2) := by
      calc
        3 ^ ((n + 1) + 2) = 3 ^ (n + 3) := by
          rw [show (n + 1) + 2 = n + 3 by ring]
        _ = 3 ^ (n + 2 + 1) := by
          rw [show n + 3 = n + 2 + 1 by ring]
        _ = 3 ^ (n + 2) * 3 ^ 1 := by rw [pow_add]
        _ = 3 ^ (n + 2) * 3 := by norm_num
        _ = 3 * 3 ^ (n + 2) := by ring
        
    rw [h_pow_4, h_pow_3]
    
    have h_expr : 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) = 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) + 13 * 4 ^ (2 * n + 1) := by
      calc
        16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) = (3 + 13) * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by norm_num
        _ = 3 * 4 ^ (2 * n + 1) + 13 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by ring
        _ = 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) + 13 * 4 ^ (2 * n + 1) := by ring
    
    rw [h_expr]
    apply dvd_add
    · exact dvd_mul_of_dvd_right ih 3
    · exact dvd_mul_of_dvd_left (dvd_refl 13) _
