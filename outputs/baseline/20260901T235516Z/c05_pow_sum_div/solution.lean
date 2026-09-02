import Mathlib

set_option exponentiation.threshold 3000

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  -- compute the remainders modulo 5
  have h2 : 2 ^ 2025 % 5 = 2 := by
    norm_num
  have h3 : 3 ^ 2025 % 5 = 3 := by
    norm_num
  -- the sum is 0 modulo 5
  have hsum : (2 ^ 2025 + 3 ^ 2025) % 5 = 0 := by
    calc
      (2 ^ 2025 + 3 ^ 2025) % 5
          = ((2 ^ 2025) % 5 + (3 ^ 2025) % 5) % 5 := by
            simpa using Nat.mod_add_mod (2 ^ 2025) (3 ^ 2025) 5
      _ = (2 + 3) % 5 := by
            simpa [h2, h3]
      _ = 0 := by norm_num
  exact Nat.dvd_of_mod_eq_zero hsum
