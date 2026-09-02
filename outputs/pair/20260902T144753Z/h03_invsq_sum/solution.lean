import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Basic

open Finset
open scoped BigOperators

/-- The classical bound `∑_{i=1}^n 1/i² ≤ 2 - 1/n` for `n ≥ 1`. -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  -- we prove a stronger statement by induction on `n`
  have h_ind :
      ∀ m : ℕ, 1 ≤ m → (∑ i ∈ Icc 1 m, (1 : ℝ) / (i : ℝ) ^ 2) ≤ 2 - 1 / (m : ℝ) := by
    intro m
    induction' m using Nat.case_strong_induction_on with m ih
    intro hm
    cases m with
    | zero =>
        exact (Nat.not_le.mpr (Nat.succ_pos 0) hm).elim
    | succ m' =>
        -- base case `m = 1`
        have h_one : m' = 0 ∨ 0 < m' := by
          rcases lt_or_eq_of_le (Nat.succ_le_of_lt (Nat.succ_pos _)) with h | rfl
          · exact Or.inr h
          · exact Or.inl rfl
        cases h_one with
        | inl hzero =>
            -- `m = 1`
            subst hzero
            simp [Icc_self, pow_two] 
        | inr hpos =>
            -- inductive step, `m = m'+1` with `m' ≥ 1`
            have hm' : 1 ≤ m' := Nat.succ_le_iff.mp (Nat.succ_le_of_lt (Nat.succ_lt_succ hpos))
            have ih' := ih m' hm'
            -- split the sum at the last element
            have hsum_split :
                (∑ i ∈ Icc 1 (m' + 1), (1 : ℝ) / (i : ℝ) ^ 2) =
                  (∑ i ∈ Icc 1 m', (1 : ℝ) / (i : ℝ) ^ 2) + (1 : ℝ) / ((m' + 1 : ℝ) ^ 2) := by
              simpa [Nat.succ_eq_add_one, add_comm] using
                (sum_Icc_succ_top (by decide) (fun i : ℕ => (1 : ℝ) / (i : ℝ) ^ 2))
            -- bound the new term by a telescoping difference
            have hterm :
                (1 : ℝ) / ((m' + 1 : ℝ) ^ 2) ≤
                  (1 : ℝ) / ((m' : ℝ) * (m' + 1 : ℝ)) := by
              have hpos1 : (0 : ℝ) < (m' + 1 : ℝ) :=
                by exact_mod_cast (Nat.succ_pos _)
              have hpos2 : (0 : ℝ) < (m' : ℝ) :=
                by exact_mod_cast (Nat.succ_pos _)
              have hle : ((m' : ℝ) * (m' + 1 : ℝ)) ≤ ((m' + 1 : ℝ) * (m' + 1 : ℝ)) := by
                have : (m' : ℝ) ≤ (m' + 1 : ℝ) := by
                  have : (m' : ℕ) ≤ m' + 1 := Nat.le_succ _
                  exact_mod_cast this
                have hnonneg : (0 : ℝ) ≤ (m' + 1 : ℝ) := le_of_lt hpos1
                exact mul_le_mul_of_nonneg_right this hnonneg
              have hpos_mul : (0 : ℝ) < ((m' + 1 : ℝ) * (m' + 1 : ℝ)) :=
                mul_pos hpos1 hpos1
              have hpos_mul' : (0 : ℝ) < ((m' : ℝ) * (m' + 1 : ℝ)) :=
                mul_pos hpos2 hpos1
              have := (one_div_le_one_div_of_le hpos_mul' hle)
              simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
            have htel :
                (∑ i ∈ Icc 1 m', (1 : ℝ) / ((i - 1 : ℝ) * (i : ℝ))) =
                  1 - 1 / (m' : ℝ) := by
              -- rewrite the sum as a telescoping series
              have : (∑ i ∈ Icc 2 (m' + 1),
                  (1 : ℝ) / ((i - 1 : ℝ) * (i : ℝ))) =
                  1 - 1 / ((m' + 1 : ℝ)) := by
                -- shift index j = i-1
                have hsum :
                    (∑ i ∈ Icc 2 (m' + 1),
                        (1 : ℝ) / ((i - 1 : ℝ) * (i : ℝ))) =
                      ∑ j ∈ Icc 1 m',
                        (1 : ℝ) / ((j : ℝ) * ((j + 1 : ℝ))) := by
                  refine sum_bij' (fun i hi => i - 1) ?_ ?_ ?_ ?_
                  · intro i hi
                    have : 1 ≤ i := (mem_Icc).1 hi).1
                    have : i - 1 ≤ m' := by
                      have : i ≤ m' + 1 := ((mem_Icc).1 hi).2
                      exact Nat.sub_le_sub_right this 1
                    exact ⟨by
                      have : 1 ≤ i - 1 + 1 := Nat.succ_le_of_lt (Nat.succ_lt_succ (Nat.succ_pos _))
                      exact this, by
                      have : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.succ_pos _))
                      simpa [this]⟩
                  · intro i hi; intro j hj; intro h; dsimp at h; linarith
                  · intro j hj; refine ⟨j+1, ?_, ?_⟩
                    · have : (1 : ℕ) ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le _)
                      have : j + 1 ≤ m' + 1 := Nat.succ_le_succ ((mem_Icc).1 hj).2
                      exact ⟨this, this⟩
                    · simp
                  · intro i hi; rfl
                have htel' :
                    (∑ j ∈ Icc 1 m',
                        (1 : ℝ) / ((j : ℝ) * ((j + 1 : ℝ)))) =
                      1 - 1 / ((m' : ℝ) + 1) := by
                  have : (∑ j ∈ Icc 1 m',
                        (1 : ℝ) / ((j : ℝ) * ((j + 1 : ℝ)))) =
                        ∑ j ∈ Icc 1 m',
                          ((1 : ℝ) / (j : ℝ) - (1 : ℝ) / ((j + 1 : ℝ))) := by
                    apply sum_congr rfl
                    intro j hj
                    have hposj : (0 : ℝ) < (j : ℝ) := by
                      have : 0 < j := Nat.succ_le_iff.mp ((mem_Icc).1 hj).1
                      exact_mod_cast this
                    have hposj1 : (0 : ℝ) < ((j + 1 : ℝ)) := by
                      exact_mod_cast (Nat.succ_pos _)
                    field_simp [hposj.ne', hposj1.ne']
                  have : (∑ j ∈ Icc 1 m',
                        ((1 : ℝ) / (j : ℝ) - (1 : ℝ) / ((j + 1 : ℝ)))) =
                        (1 : ℝ) - (1 : ℝ) / ((m' + 1 : ℝ)) := by
                    have : (∑ j ∈ Icc 1 m',
                          ((1 : ℝ) / (j : ℝ))) -
                          (∑ j ∈ Icc 1 m',
                          ((1 : ℝ) / ((j + 1 : ℝ)))) =
                          (1 : ℝ) - (1 : ℝ) / ((m' + 1 : ℝ)) := by
                      have h1 : (∑ j ∈ Icc 1 m', (1 : ℝ) / (j : ℝ)) =
                        ∑ j ∈ Icc 1 m', (1 : ℝ) / (j : ℝ) := rfl
                      have h2 : (∑ j ∈ Icc 1 m', (1 : ℝ) / ((j + 1 : ℝ))) =
                        ∑ j ∈ Icc 2 (m' + 1), (1 : ℝ) / (j : ℝ) := by
                        refine sum_bij' (fun j _ => j + 1) ?_ ?_ ?_ ?_
                        · intro j hj; exact ⟨by
                            have : (1 : ℕ) ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le _)
                            have : j + 1 ≤ m' + 1 := Nat.succ_le_succ ((mem_Icc).1 hj).2
                            exact ⟨this, this⟩, by rfl⟩
                        · intro a ha b hb h; dsimp at h; linarith
                        · intro b hb; refine ⟨b - 1, ?_, ?_⟩
                          · have : (1 : ℕ) ≤ b - 1 := Nat.sub_le_iff_le_add.mp (Nat.le_of_lt_succ ?_)
                            sorry
                          · simp
                        · intro j hj; rfl
                      sorry
                    sorry
                  sorry
                simpa [hsum] using htel'
              simpa using this
            have : (∑ i ∈ Icc 1 (m' + 1), (1 : ℝ) / (i : ℝ) ^ 2) ≤
                (∑ i ∈ Icc 1 m', (1 : ℝ) / (i : ℝ) ^ 2) + (1 : ℝ) / ((m' : ℝ) * (m' + 1 : ℝ)) := by
              simpa [hsum_split] using add_le_add_right ih' _
            have : (∑ i ∈ Icc 1 (m' + 1), (1 : ℝ) / (i : ℝ) ^ 2) ≤
                (2 - 1 / (m' : ℝ)) + (1 : ℝ) / ((m' : ℝ) * (m' + 1 : ℝ)) := by
              exact le_trans this (add_le_add_right ih' _)
            have : (∑ i ∈ Icc 1 (m' + 1), (1 : ℝ) / (i : ℝ) ^ 2) ≤
                2 - 1 / ((m' + 1 : ℝ)) := by
              have hcalc :
                  (2 - 1 / (m' : ℝ)) + (1 : ℝ) / ((m' : ℝ) * (m' + 1 : ℝ))
                    = 2 - 1 / ((m' + 1 : ℝ)) := by
                field_simp
              simpa [hcalc] using this
            exact this
  exact h_ind n hn
