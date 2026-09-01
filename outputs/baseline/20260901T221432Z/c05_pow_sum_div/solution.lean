import Mathlib
open Nat

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  -- First show the sum is congruent to `0` modulo `5`.
  have hmod : (2 ^ 2025 + 3 ^ 2025) % 5 = 0 := by
    norm_num
  -- Convert the modular statement to a divisibility statement.
  exact Nat.dvd_of_mod_eq_zero hmod
