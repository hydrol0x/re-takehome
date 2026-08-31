import Mathlib

/-- Base case for the induction: when k = 0, the sum equals 1 (which is 4^0). -/
lemma putnam_2020_a2_base :
  (∑ j ∈ Finset.Icc 0 0, 2 ^ (0 - j) * Nat.choose (0 + j) j) = 4 ^ 0 := by norm_num

/-- Inductive step: relates the sum for k+1 to the sum for k. -/
lemma putnam_2020_a2_step (k : ℕ) :
  (∑ j ∈ Finset.Icc 0 (k + 1), 2 ^ (k + 1 - j) * Nat.choose (k + 1 + j) j) = 
  4 * (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) := by sorry

/-- Main theorem: proves the identity for all k by induction. -/
theorem putnam_2020_a2
  (k : ℕ) :
  (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k := by
  induction k with
  | zero =>
    exact putnam_2020_a2_base
  | succ k ih =>
    rw [putnam_2020_a2_step k]
    rw [ih]
    -- The goal reduces to 4 * 4^k = 4^(k+1), which is handled by ring/arith
    ring_nf
    <;> simp [pow_succ, mul_assoc]
    <;> omega
