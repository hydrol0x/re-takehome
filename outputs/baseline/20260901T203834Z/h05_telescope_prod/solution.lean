import Mathlib

open Finset

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  -- Prove a more general statement by induction on `m ≥ 2`.
  have h_general :
      ∀ m : ℕ, 2 ≤ m →
        ∏ k ∈ Icc 2 m, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((m : ℝ) + 1) / (2 * (m : ℝ)) := by
    intro m
    refine Nat.le_induction ?base ?step ?hm
    · -- base case `m = 2`
      have : (∏ k ∈ Icc 2 (2 : ℕ), ((1 : ℝ) - 1 / (k : ℝ) ^ 2)) =
          ((2 : ℝ) + 1) / (2 * (2 : ℝ)) := by
        simp
      simpa using this
    · intro m hm ih
      -- use the product formula for `Icc 2 (m+1)`
      have hprod :
          ∏ k ∈ Icc 2 (m + 1), ((1 : ℝ) - 1 / (k : ℝ) ^ 2) =
            (∏ k ∈ Icc 2 m, ((1 : ℝ) - 1 / (k : ℝ) ^ 2)) *
              ((1 : ℝ) - 1 / ((m + 1 : ℝ) ^ 2)) := by
        -- `prod_Icc_succ_top` gives exactly this decomposition
        simpa [Nat.succ_eq_add_one] using
          (prod_Icc_succ_top (a := 2) (b := m)
            (f := fun k : ℕ => ((1 : ℝ) - 1 / (k : ℝ) ^ 2)) hm)
      -- replace the left part using the induction hypothesis
      have hcalc :
          ∏ k ∈ Icc 2 (m + 1), ((1 : ℝ) - 1 / (k : ℝ) ^ 2) =
            ((m : ℝ) + 1) / (2 * (m : ℝ)) *
              ((1 : ℝ) - 1 / ((m + 1 : ℝ) ^ 2)) := by
        simpa [ih] using hprod
      -- simplify the algebraic expression
      have : ((m : ℝ) + 1) / (2 * (m : ℝ)) *
            ((1 : ℝ) - 1 / ((m + 1 : ℝ) ^ 2)) =
          ((m + 1 : ℝ) + 1) / (2 * ((m + 1 : ℝ))) := by
        field_simp [pow_two] -- expands and simplifies the rational expression
        ring
      simpa [Nat.succ_eq_add_one] using this
  exact h_general n hn
