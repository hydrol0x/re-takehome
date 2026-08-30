import Mathlib

open Finset

theorem putnam_2020_a2
  (k : ℕ) :
  (∑ j ∈ Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k := by
  classical
  -- `Icc 0 k` is the same as `range (k+1)`
  have h_range : (Icc 0 k) = range (k + 1) := by
    ext j
    simp [Finset.mem_Icc, Nat.lt_succ_iff]
  -- use the existing lemma `Nat.sum_mul_choose_eq_pow_two`
  simpa [h_range] using Nat.sum_mul_choose_eq_pow_two k
