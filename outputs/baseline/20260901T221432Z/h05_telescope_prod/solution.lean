import Mathlib

open Finset

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  -- auxiliary lemma proved by induction on `n`
  have h :
      ∀ m : ℕ, 2 ≤ m →
        ∏ k ∈ Icc 2 m, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((m : ℝ) + 1) / (2 * (m : ℝ)) := by
    intro m
    intro hm
    -- analyse the shape of `m`
    cases m with
    | zero => cases hm
    | succ m1 =>
      cases m1 with
      | zero => cases hm
      | succ m2 =>
        -- now `m = m2 + 2`
        have hm2 : 2 ≤ m2 + 2 := hm
        -- induction hypothesis for `m2 + 1`
        have ih :
            ∏ k ∈ Icc 2 (m2 + 1), ((1 : ℝ) - 1 / (k : ℝ) ^ 2) =
              ((m2 + 1 : ℝ) + 1) / (2 * (m2 + 1 : ℝ)) := by
          apply h (m2 + 1)
          have : (2 : ℕ) ≤ m2 + 1 := by
            have : (0 : ℕ) ≤ m2 := Nat.zero_le _
            exact Nat.succ_le_succ (Nat.succ_le_succ this)
          exact this
        -- split the product at the last element
        have hsplit :
            ∏ k ∈ Icc 2 (m2 + 2), ((1 : ℝ) - 1 / (k : ℝ) ^ 2) =
              (∏ k ∈ Icc 2 (m2 + 1), ((1 : ℝ) - 1 / (k : ℝ) ^ 2)) *
                ((1 : ℝ) - 1 / ((m2 + 2 : ℝ) ^ 2)) := by
          have : (2 : ℕ) ≤ m2 + 1 := by
            have : (0 : ℕ) ≤ m2 := Nat.zero_le _
            exact Nat.succ_le_succ (Nat.succ_le_succ this)
          simpa using
            (Finset.prod_Icc_succ_top (a := 2) (b := m2 + 1)
                (f := fun k : ℕ => ((1 : ℝ) - 1 / (k : ℝ) ^ 2))
                (h := this))
        -- combine the induction hypothesis with the last factor
        calc
          ∏ k ∈ Icc 2 (m2 + 2), ((1 : ℝ) - 1 / (k : ℝ) ^ 2)
              = (∏ k ∈ Icc 2 (m2 + 1), ((1 : ℝ) - 1 / (k : ℝ) ^ 2)) *
                ((1 : ℝ) - 1 / ((m2 + 2 : ℝ) ^ 2)) := by
                simpa using hsplit
          _ = ((m2 + 1 : ℝ) + 1) / (2 * (m2 + 1 : ℝ)) *
                ((1 : ℝ) - 1 / ((m2 + 2 : ℝ) ^ 2)) := by
                simpa [ih]
          _ = ((m2 + 2 : ℝ) + 1) / (2 * (m2 + 2 : ℝ)) := by
                have hpos : (m2 + 2 : ℝ) ≠ 0 := by
                  have : (0 : ℝ) < (m2 + 2 : ℝ) := by
                    have : (0 : ℕ) < m2 + 2 := Nat.succ_lt_succ (Nat.succ_pos _)
                    exact_mod_cast this
                  exact ne_of_gt this
                field_simp [pow_two, hpos] 
  exact h n hn
