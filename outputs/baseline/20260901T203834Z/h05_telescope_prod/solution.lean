import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Nat.Factorial
import Mathlib.Tactic.FieldSimp

open Finset

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  classical
  -- rewrite each factor
  have h_factor :
      ∀ k ∈ Icc 2 n,
        (1 : ℝ) - 1 / (k : ℝ) ^ 2 =
          ((k : ℝ) - 1) / k * ((k : ℝ) + 1) / k := by
    intro k hk
    have hkpos : 0 < k := Nat.lt_of_lt_of_le (Nat.zero_lt_two) ((mem_Icc).1 hk).1
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
    field_simp [pow_two, hk0] ; ring
  -- replace the product by the factored form
  have h_prod :
      ∏ k ∈ Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^
