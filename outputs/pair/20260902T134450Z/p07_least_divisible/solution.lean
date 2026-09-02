import Mathlib
import Mathlib.Tactic.IntervalCases

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  refine ⟨?mem, ?lb⟩
  -- membership of 19
  have hpos : (0 : ℕ) < 19 := by decide
  have hdiv : 77 ∣ (19 + 2) * (19 + 3) := by
    norm_num
  exact ⟨hpos, hdiv⟩
  -- lower bound: any other element is at least 19
  intro n hn
  rcases hn with ⟨hnpos, hndiv⟩
  by_contra hlt
  have hlt' : n < 19 := Nat.lt_of_not_ge hlt
  have : ¬ 77 ∣ (n + 2) * (n + 3) := by
    interval_cases n <;> norm_num
  exact this hndiv
