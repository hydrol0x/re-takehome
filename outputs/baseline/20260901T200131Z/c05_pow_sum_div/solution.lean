import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  norm_num [Nat.pow_mod, Nat.add_mod]
