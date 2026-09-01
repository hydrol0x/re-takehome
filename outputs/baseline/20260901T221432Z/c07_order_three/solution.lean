import Mathlib
import Mathlib.Tactic.IntervalCases

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`.
Must be a numeric literal. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  -- `5` belongs to the set
  have hmem : (0 : ℕ) < c07_answer ∧ (11 : ℕ) ∣ 3 ^ c07_answer - 1 := by
    constructor
    · decide
    · norm_num
  refine ⟨hmem, ?_⟩
  intro n hn
  rcases hn with ⟨hnpos, hndiv⟩
  -- prove `5 ≤ n`
  have : (c07_answer : ℕ) ≤ n := by
    by_contra hlt
    have hlt' : n < c07_answer := Nat.not_le.mp hlt
    have hle4 : n ≤ 4 := by
      have : n < 5 := hlt'
      exact (Nat.lt_succ_iff).mp this
    have hmod0 : (3 ^ n - 1) % 11 = 0 := Nat.mod_eq_zero_of_dvd hndiv
    have hmod_ne : (3 ^ n - 1) % 11 ≠ 0 := by
      interval_cases n using hnpos hle4
      · cases hnpos
      · norm_num
      · norm_num
      · norm_num
      · norm_num
    exact (hmod_ne hmod0).elim
  exact this
