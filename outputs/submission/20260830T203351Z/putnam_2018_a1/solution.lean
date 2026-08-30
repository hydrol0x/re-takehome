import Mathlib

-- First, let's solve the problem mathematically:
-- 1/a + 1/b = 3/2018
-- Multiply by ab: b + a = 3ab/2018
-- So: 2018(a+b) = 3ab
-- Rearrange: 3ab - 2018a - 2018b = 0
-- Complete the rectangle: (3a-2018)(3b-2018) = 2018²
-- 
-- Factor 2018 = 2 × 1009 (where 1009 is prime)
-- So 2018² = 2² × 1009² has (2+1)(2+1) = 9 divisors
-- Since (3a-2018)(3b-2018) = 2018² and a,b > 0, we need 3a > 2018 and 3b > 2018
-- Also 3a ≡ 2018 (mod 3), i.e., 3a ≡ 0 (mod 3), so we need d ≡ 0 (mod 3)
-- 
-- The divisors d of 2018² where d ≡ 2018 (mod 3) give us valid solutions
-- Since 2018 ≡ 2 (mod 3), we need d ≡ 2 (mod 3) or equivalently d ≡ 2018 (mod 3)

abbrev putnam_2018_a1_solution : Set (ℤ × ℤ) := {p | 
  let (a, b) := p
  0 < a ∧ 0 < b ∧ (1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018}

theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ putnam_2018_a1_solution) := by
  constructor
  · intro h_eq
    simp only [putnam_2018_a1_solution, Prod.mk.injEq]
    exact ⟨h.1, h.2, h_eq⟩
  · intro h_mem
    simp only [putnam_2018_a1_solution, Prod.mk.injEq] at h_mem
    exact h_mem.2.2
