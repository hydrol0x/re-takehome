import Mathlib

/-- The least positive integer `n` such that `2 ^ n` leaves remainder `1` when
divided by `25`. Must be a numeric literal. -/
abbrev m02_answer : ℕ := 20

/-- `m02_answer` is the least element of the set of positive `n` with
`2 ^ n % 25 = 1`; that is, the multiplicative order of `2` modulo `25`. -/
theorem m02_ord25 : IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 25 = 1} m02_answer := by
  constructor
  · -- Show 20 is in the set
    simp [m02_answer]
    norm_num
  · -- Show 20 is minimal
    intro k hk
    simp only [Set.mem_setOf_eq, m02_answer] at hk ⊢
    have h₁ : 0 < k := hk.1
    have h₂ : 2 ^ k % 25 = 1 := hk.2
    have h₃ : 20 ≤ k := by
      by_contra h
      have h₄ : k < 20 := lt_of_le_of_ne (le_of_not_gt h) (by omega)
      interval_cases k <;> norm_num at h₂ ⊢ <;> try contradiction
    exact h₃
