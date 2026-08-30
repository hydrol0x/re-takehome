import Mathlib
import Mathlib.Tactic.IntervalCases

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Prove p07_answer is in the set
    simp only [p07_answer, Set.mem_setOf_eq]
    norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Prove p07_answer is the least
    intro m hm
    rw [p07_answer]
    by_contra h
    have h_pos : 0 < m := hm.1
    have h_dvd : 77 ∣ (m + 2) * (m + 3) := hm.2
    have h_lt : m < 19 := by omega
    
    -- Check all cases from 0 to 18
    interval_cases m <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h_dvd <;> cases h_dvd
