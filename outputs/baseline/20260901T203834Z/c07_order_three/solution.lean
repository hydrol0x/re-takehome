import Mathlib
import Mathlib.Tactic.IntervalCases

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`.
Must be a numeric literal. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  refine ⟨?_, ?_⟩
  · -- membership of `5`
    have hpos : (0 : ℕ) < 5 := by decide
    have hdiv : (11 : ℕ) ∣ 3 ^ 5 - 1 := by norm_num
    exact ⟨hpos, hdiv⟩
  · -- minimality
    intro n hn
    rcases hn with ⟨hnpos, hdiv⟩
    have h5le : (5 : ℕ) ≤ n := by
      by_contra hlt
      have hlt' : n < 5 := Nat.lt_of_not_ge hlt
      interval_cases n
      · -- n = 0
        have : (0 : ℕ) < 0 := by
          simpa using hnpos
        exact (lt_irrefl _ this).elim
      · -- n = 1
        have hdiv' : (11 : ℕ) ∣ 3 ^ 1 - 1 := by
          simpa using hdiv
        have hnot : ¬ (11 : ℕ) ∣ 3 ^ 1 - 1 := by norm_num
        exact hnot hdiv'
      · -- n = 2
        have hdiv' : (11 : ℕ) ∣ 3 ^ 2 - 1 := by
          simpa using hdiv
        have hnot : ¬ (11 : ℕ) ∣ 3 ^ 2 - 1 := by norm_num
        exact hnot hdiv'
      · -- n = 3
        have hdiv' : (11 : ℕ) ∣ 3 ^ 3 - 1 := by
          simpa using hdiv
        have hnot : ¬ (11 : ℕ) ∣ 3 ^ 3 - 1 := by norm_num
        exact hnot hdiv'
      · -- n = 4
        have hdiv' : (11 : ℕ) ∣ 3 ^ 4 - 1 := by
          simpa using hdiv
        have hnot : ¬ (11 : ℕ) ∣ 3 ^ 4 - 1 := by norm_num
        exact hnot hdiv'
    exact h5le
