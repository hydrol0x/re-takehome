import Mathlib

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- The least positive integer `n` such that `2 ^ n` leaves remainder `1` when
divided by `25`. Must be a numeric literal. -/
abbrev m02_answer : ℕ := 20

/-- `m02_answer` is the least element of the set of positive `n` with
`2 ^ n % 25 = 1`; that is, the multiplicative order of `2` modulo `25`. -/
theorem m02_ord25 : IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 25 = 1} m02_answer := by
  constructor
  · -- Prove m02_answer is in the set
    constructor
    · -- 0 < 20
      norm_num
    · -- 2^20 % 25 = 1
      norm_num
  · -- Prove m02_answer is the least
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    rcases hn with ⟨hn_pos, hn_mod⟩
    by_contra h
    push_neg at h
    have hlt : n < 20 := by omega
    interval_cases n <;>
      norm_num at hn_pos hn_mod <;>
      omega
