import Mathlib

theorem putnam_2020_a2
  (k : ℕ) :
  (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k := by
  have h_base : (∑ j ∈ Finset.Icc 0 0, 2 ^ (0 - j) * Nat.choose (0 + j) j) = 4 ^ 0 := by norm_num
  have h_inductive_step : ∀ k : ℕ, (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k → 
    (∑ j ∈ Finset.Icc 0 (k + 1), 2 ^ ((k + 1) - j) * Nat.choose ((k + 1) + j) j) = 4 ^ (k + 1) := by sorry
  have h_main : ∀ k : ℕ, (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k := by sorry
  exact h_main k
