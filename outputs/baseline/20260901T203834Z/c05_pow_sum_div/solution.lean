import Mathlib

set_option exponentiation.threshold 10000

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  -- Reduce the goal to a statement about remainders.
  apply (Nat.dvd_iff_mod_eq_zero).mpr
  have h2 : (2 ^ 2025) % 5 = 2 := by
    norm_num
  have h3 : (3 ^ 2025) % 5 = 3 := by
    norm_num
  calc
    (2 ^ 2025 + 3 ^ 2025) % 5
        = ((2 ^ 2025) % 5 + (3 ^ 2025) % 5) % 5 := by
          simpa using Nat.add_mod (2 ^ 2025) (3 ^ 2025) 5
    _ = (2 + 3) % 5 := by
          simpa [h2, h3]
    _ = 0 := by
          norm_num
