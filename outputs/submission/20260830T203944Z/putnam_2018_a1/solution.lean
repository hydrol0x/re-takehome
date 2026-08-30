import Mathlib

-- putnam_2018_a1_solution is the set of ordered pairs (a,b) of positive integers
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
  · -- Forward direction: if the equation holds, then (a,b) is in the solution set
    intro h_eq
    exact ⟨h.1, h.2, h_eq⟩
  · -- Backward direction: if (a,b) is in the solution set, then the equation holds
    rintro ⟨ha_pos, hb_pos, h_eq⟩
    exact h_eq
