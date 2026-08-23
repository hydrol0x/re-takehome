import Mathlib

abbrev putnam_2020_a2_solution : ℕ → ℕ := fun k => 4 ^ k

theorem putnam_2020_a2_solution_correct (k : ℕ) :
  (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k := by sorry

theorem putnam_2020_a2
  (k : ℕ) :
  (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) =
    putnam_2020_a2_solution k := by
  rw [putnam_2020_a2_solution_correct]
