import Mathlib

/-- The classical bound `∑_{i=1}^n 1/i² ≤ 2 - 1/n` for `n ≥ 1`. -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  have h_main : ∀ k : ℕ, 1 ≤ k → ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (k : ℝ) := by
    intro k hk
    induction' hk with k hk IH
    · -- Base case: k = 1
      norm_num [Finset.sum_Icc_succ_top]
    · -- Inductive step
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k.succ)]
      have h₁ : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero fun h => by simp_all
      have h₂ : 0 < (k : ℝ) + 1 := by positivity
      have h₃ : 0 < ((k : ℝ) + 1) ^ 2 := by positivity
      -- Need to show: 2 - 1/k + 1/(k+1)² ≤ 2 - 1/(k+1)
      -- Equivalently: 1/(k+1)² ≤ 1/k - 1/(k+1) = 1/(k(k+1))
      -- Equivalently: k ≤ k+1
      have h₄ : (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) := by
        apply one_div_le_one_div_of_le
        · positivity
        · have : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
          nlinarith
      have h₅ : (1 : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)) = (1 : ℝ) / (k : ℝ) - (1 : ℝ) / ((k : ℝ) + 1) := by
        field_simp [h₁.ne', h₂.ne']
        ring
      calc
        ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ 2 + (1 : ℝ) / (k.succ : ℝ) ^ 2
          ≤ (2 - 1 / (k : ℝ)) + (1 : ℝ) / (k.succ : ℝ) ^ 2 := by gcongr
        _ = 2 - 1 / (k : ℝ) + (1 : ℝ) / (k.succ : ℝ) ^ 2 := by ring
        _ ≤ 2 - 1 / (k : ℝ) + ((1 : ℝ) / (k : ℝ) - (1 : ℝ) / (k.succ : ℝ)) := by
          gcongr
          <;> norm_num at *
          <;> simp_all [Nat.cast_add, Nat.cast_one]
          <;> try field_simp [h₁.ne', h₂.ne']
          <;> nlinarith
        _ = 2 - 1 / (k.succ : ℝ) := by ring
  exact h_main n hn
