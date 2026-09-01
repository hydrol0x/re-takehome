import Mathlib

-- Helper: Base case k = 0
lemma putnam_2020_a2_base :
  (∑ j ∈ Finset.Icc 0 0, 2 ^ (0 - j) * Nat.choose (0 + j) j) = 4 ^ 0 := by
  norm_num

-- Helper: Inductive step relation
-- Relates the sum for k+1 to the sum for k.
lemma putnam_2020_a2_inductive_step (k : ℕ) 
  (h : (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k) :
  (∑ j ∈ Finset.Icc 0 (k + 1), 2 ^ ((k + 1) - j) * Nat.choose ((k + 1) + j) j) = 4 ^ (k + 1) := by sorry

-- Main theorem
theorem putnam_2020_a2
  (k : ℕ) :
  (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k := by
  induction k with
  | zero => exact putnam_2020_a2_base
  | succ k ih =>
    -- Apply the inductive step helper
    have h_step := putnam_2020_a2_inductive_step k ih
    exact h_step
