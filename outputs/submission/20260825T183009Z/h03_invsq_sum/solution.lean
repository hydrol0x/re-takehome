import Mathlib

open Finset

/-- Positivity of the real cast of a natural number n given 1 ≤ n -/
lemma pos_nat_cast_of_ge_one (n : ℕ) (hn : 1 ≤ n) : 0 < (n : ℝ) := by positivity

/-- The algebraic inequality used for the induction step: 1/(n+1)^2 ≤ 1/n - 1/(n+1) -/
lemma inv_sq_induction_inequality (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / ((n + 1 : ℝ) ^ 2) ≤ (1 : ℝ) / (n : ℝ) - (1 : ℝ) / ((n + 1 : ℝ)) := by sorry

/-- Base case: When n = 1, the sum equals the bound -/
lemma inv_sq_base_case (n : ℕ) (h : n = 1) :
    ∑ i ∈ Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 = 2 - 1 / (n : ℝ) := by sorry

theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by sorry
