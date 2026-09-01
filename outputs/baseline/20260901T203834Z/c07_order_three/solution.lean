import Mathlib

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`.
Must be a numeric literal. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  change IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} 5
  refine And.intro ?hmem ?hmin
  · -- 5 belongs to the set
    have hpos : (0 : ℕ) < 5 := by decide
    have hdiv : 11 ∣ 3 ^ 5 - 1 := by
      norm_num
    exact And.intro hpos hdiv
  · -- minimality
    intro n hn
    rcases hn with ⟨hnpos, hndiv⟩
    have h5le : (5 : ℕ) ≤ n := by
      by_contra hlt
      have hlt' : n < 5 := Nat.not_le.mp hlt
      have : False := by
        interval_cases n using Nat with
        | zero =>
            simpa using hnpos
        | one =>
            have : (11 : ℕ) ∣ 3 ^ (1) - 1 := by
              simpa using hndiv
            have : False := by
              have h : ¬ (11 : ℕ) ∣ 3 ^ (1) - 1 := by decide
              exact h this
            exact this
        | two =>
            have : (11 : ℕ) ∣ 3 ^ (2) - 1 := by
              simpa using hndiv
            have : False := by
              have h : ¬ (11 : ℕ) ∣ 3 ^ (2) - 1 := by decide
              exact h this
            exact this
        | three =>
            have : (11 : ℕ) ∣ 3 ^ (3) - 1 := by
              simpa using hndiv
            have : False := by
              have h : ¬ (11 : ℕ) ∣ 3 ^ (3) - 1 := by decide
              exact h this
            exact this
        | four =>
            have : (11 : ℕ) ∣ 3 ^ (4) - 1 := by
              simpa using hndiv
            have : False := by
              have h : ¬ (11 : ℕ) ∣ 3 ^ (4) - 1 := by decide
              exact h this
            exact this
      exact this
    exact h5le
