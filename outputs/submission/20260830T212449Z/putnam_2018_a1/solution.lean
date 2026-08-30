import Mathlib

-- Define the solution set containing all ordered pairs (a,b) of positive integers
-- satisfying the equation 1/a + 1/b = 3/2018
abbrev putnam_2018_a1_solution : Set (ℤ × ℤ) := {p | 
  let (a, b) := p
  0 < a ∧ 0 < b ∧ (1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018}

theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ putnam_2018_a1_solution) := by
  constructor
  · -- Forward direction: if equation holds, then (a,b) is in the solution set
    intro eq
    simp only [putnam_2018_a1_solution, Prod.mk.injEq]
    refine' ⟨h.1, h.2, _⟩
    exact eq
  · -- Backward direction: if (a,b) is in the solution set, then equation holds
    rintro ⟨ha, hb, eq⟩
    exact eq
