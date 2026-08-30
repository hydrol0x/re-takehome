import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  refine ⟨?mem, ?least⟩
  · -- membership of 19
    have hpos : (0 : ℕ) < 19 := by decide
    have hdiv : 77 ∣ (19 + 2) * (19 + 3) := by
      norm_num
    exact And.intro hpos hdiv
  · -- minimality
    intro n hn
    by_contra hnot
    have hlt : n < 19 := Nat.lt_of_not_ge hnot
    have hfalse : ¬ ∃ m < 19, 0 < m ∧ 77 ∣ (m + 2) * (m + 3) := by decide
    exact hfalse ⟨n, hlt, hn⟩
