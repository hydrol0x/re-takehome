import Mathlib

-- The set of all ordered pairs of positive integers satisfying the equation.
abbrev putnam_2018_a1_solution : Set (ℤ × ℤ) :=
  {p | (0 < p.1) ∧ (0 < p.2) ∧ ((1 : ℚ) / p.1 + (1 : ℚ) / p.2 = (3 : ℚ) / 2018)}

theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ putnam_2018_a1_solution) := by
  constructor
  · intro h_eq
    exact ⟨h.1, h.2, h_eq⟩
  · intro h_mem
    exact h_mem.2.2
