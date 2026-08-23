import Mathlib

-- First, let's characterize the solution set mathematically
-- The equation 1/a + 1/b = 3/2018 with positive integers a,b is equivalent to:
-- 2018*(a + b) = 3*a*b
-- which rearranges to (3*a - 2018)*(3*b - 2018) = 2018^2

abbrev putnam_2018_a1_solution : Set (ℤ × ℤ) := 
  {p | let (a, b) := p
       0 < a ∧ 0 < b ∧ 2018 * (a + b) = 3 * a * b}

theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ putnam_2018_a1_solution) := by
  constructor
  · -- Forward direction: equation implies membership in solution set
    intro heq
    rw [putnam_2018_a1_solution]
    constructor
    · exact h.1
    constructor
    · exact h.2
    · -- Convert rational equation to integer equation
      have h₁ : (1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018 := heq
      field_simp [h.1.ne', h.2.ne'] at h₁
      norm_cast at h₁
      ring_nf at h₁
      linarith
  · -- Reverse direction: membership in solution set implies equation
    intro hmem
    rw [putnam_2018_a1_solution] at hmem
    have h₁ : 0 < a := hmem.1
    have h₂ : 0 < b := hmem.2.1
    have h₃ : 2018 * (a + b) = 3 * a * b := hmem.2.2
    -- Convert integer equation back to rational equation
    have h₄ : (1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018 := by
      field_simp [h₁.ne', h₂.ne']
      norm_cast
      <;> ring_nf at h₃ ⊢ <;> linarith
    exact h₄
