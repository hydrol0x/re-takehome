import Mathlib
import Mathlib.Tactic.IntervalCases

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`.
Must be a numeric literal. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  refine ⟨?mem, ?least⟩
  · -- membership of 5
    have hpos : (0 : ℕ) < 5 := by decide
    have hdiv : 11 ∣ 3 ^ 5 - 1 := by
      norm_num
    exact ⟨hpos, hdiv⟩
  · -- minimality
    intro n hn
    rcases hn with ⟨hnpos, hndiv⟩
    have hlt_or : n < 5 ∨ 5 ≤ n := lt_or_ge n 5
    cases hlt_or with
    | inl hlt =>
        have : False := by
          have hle4 : n ≤ 4 := Nat.le_of_lt_succ hlt
          interval_cases n using Nat
          · -- n = 0
            exact (lt_irrefl (0 : ℕ) hnpos).elim
          · -- n = 1
            have : ¬ 11 ∣ 3 ^ 1 - 1 := by norm_num
            exact this hndiv
          · -- n = 2
            have : ¬ 11 ∣ 3 ^ 2 - 1 := by norm_num
            exact this hndiv
          · -- n = 3
            have : ¬ 11 ∣ 3 ^ 3 - 1 := by norm_num
            exact this hndiv
          · -- n = 4
            have : ¬ 11 ∣ 3 ^ 4 - 1 := by norm_num
            exact this hndiv
        exact (False.elim this)
    | inr hge => exact hge
