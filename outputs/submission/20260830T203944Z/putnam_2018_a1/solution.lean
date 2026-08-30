import Mathlib

-- The set of all ordered pairs (a,b) of positive integers satisfying 1/a + 1/b = 3/2018
abbrev putnam_2018_a1_solution : Set (ℤ × ℤ) := 
  {p | 0 < p.1 ∧ 0 < p.2 ∧ (1 : ℚ) / p.1 + (1 : ℚ) / p.2 = (3 : ℚ) / 2018}

theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ putnam_2018_a1_solution) := by
  constructor
  · intro h_eq
    refine' ⟨h.1, h.2, _⟩
    exact h_eq
  · rintro ⟨ha, hb, h_eq⟩
    exact h_eq
