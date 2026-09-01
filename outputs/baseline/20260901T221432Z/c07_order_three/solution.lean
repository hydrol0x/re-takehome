import Mathlib
import Mathlib.Tactic.IntervalCases

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  refine ⟨?mem, ?least⟩
  · -- `5` satisfies the condition
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
        -- `n < 5` leads to a contradiction
        have hle4 : n ≤ 4 := Nat.le_of_lt_succ hlt
        have hcases :
            n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
          interval_cases n using hle4
        -- eliminate the impossible case `n = 0`
        have hcases' : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
          cases hcases with
          | inl h0 =>
              have : False := (lt_irrefl (0 : ℕ)) (by simpa [h0] using hnpos)
              exact False.elim this
          | inr hrest => exact hrest
        -- now check the remaining possibilities
        cases hcases' with
        | inl h1 =>
            have : ¬ (11 ∣ 3 ^ 1 - 1) := by norm_num
            exact (False.elim (this hndiv))
        | inr hrest1 =>
            cases hrest1 with
            | inl h2 =>
                have : ¬ (11 ∣ 3 ^ 2 - 1) := by norm_num
                exact (False.elim (this hndiv))
            | inr hrest2 =>
                cases hrest2 with
                | inl h3 =>
                    have : ¬ (11 ∣ 3 ^ 3 - 1) := by norm_num
                    exact (False.elim (this hndiv))
                | inr hrest3 =>
                    cases hrest3 with
                    | inl h4 =>
                        have : ¬ (11 ∣ 3 ^ 4 - 1) := by norm_num
                        exact (False.elim (this hndiv))
                    | inr hge5 =>
                        exact (False.elim (Nat.not_lt_of_ge hge5 hlt))
    | inr hge => exact hge
