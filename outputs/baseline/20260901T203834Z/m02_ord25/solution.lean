import Mathlib
import Mathlib.Tactic.IntervalCases

/-- The least positive integer `n` such that `2 ^ n` leaves remainder `1` when
divided by `25`. Must be a numeric literal. -/
abbrev m02_answer : ℕ := 20

/-- `m02_answer` is the least element of the set of positive `n` with
`2 ^ n % 25 = 1`; that is, the multiplicative order of `2` modulo `25`. -/
theorem m02_ord25 : IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 25 = 1} m02_answer := by
  refine ⟨?mem, ?lb⟩
  · -- membership of 20
    have hpos : (0 : ℕ) < 20 := by decide
    have hmod : 2 ^ 20 % 25 = 1 := by
      norm_num
    exact ⟨hpos, hmod⟩
  · -- minimality
    intro n hn
    rcases hn with ⟨hnpos, hnmod⟩
    by_contra hlt
    have hlt' : n < 20 := Nat.lt_of_not_ge hlt
    have hle19 : n ≤ 19 := (Nat.lt_succ_iff).mp hlt'
    interval_cases n using hle19
    · -- case n = 0 contradicts positivity
      exact (lt_irrefl _ hnpos)
    all_goals
      have hne : (2 ^ n % 25) ≠ 1 := by
        norm_num
      exact hne hnmod
