import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

-- Helper: Direct verification that 6! < 3^6
lemma base_case : Nat.factorial 6 < 3 ^ 6 := by norm_num

-- Helper: For all k ≥ 7, k! ≥ 3^k
lemma factorial_ge_pow_from_7 : ∀ k, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by sorry

-- Helper: Inductive step - if k ≥ 7 and k! ≥ 3^k, then (k+1)! ≥ 3^(k+1)
lemma inductive_step : ∀ k, k ≥ 7 → Nat.factorial k ≥ 3 ^ k → Nat.factorial (k + 1) ≥ 3 ^ (k + 1) := by sorry

-- Main theorem
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by sorry
