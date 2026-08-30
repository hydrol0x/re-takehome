import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

open Finset

theorem rmo_2000_3
  (x : ℕ → ℝ)
  (hpos : ∀ n, 0 < x n)
  (hmono : ∀ n, x n ≥ x (n + 1))
  (hsq : ∀ N, (Ico 1 (N + 1)).sum (fun i => x (i * i) / (i : ℝ)) ≤ 1) :
  ∀ k, (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
  intro k
  by_cases hk : k = 0
  · -- Case k = 0
    rw [hk]
    simp [Ico]
    <;> norm_num
  · -- Case k > 0
    have hk' : 1 ≤ k := by
      omega
    -- Define m = floor(sqrt(k))
    set m : ℕ := Nat.sqrt k with hm_def
    have hm_sq : m * m ≤ k := Nat.sqrt_le' k
    have hm_succ_sq : (m + 1) * (m + 1) > k := by
      have := Nat.lt_succ_sqrt k
      linarith
    
    -- Split the sum into blocks [j^2, (j+1)^2)
    have h_main : (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
      -- Use the fact that x is nonincreasing to bound each block
      have h_sum_bound : 
        ∑ i ∈ Ico 1 (k + 1), x i / (i : ℝ) ≤ 
        ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) * 3 := by
        sorry
      -- Use the hypothesis about squares
      have h_squares : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
        have : (Ico 1 (m + 1)).sum (fun i => x (i * i) / (i : ℝ)) ≤ 1 := hsq m
        simpa [hm_def] using this
      calc
        ∑ i ∈ Ico 1 (k + 1), x i / (i : ℝ) ≤ ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) * 3 := h_sum_bound
        _ = 3 * ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) := by ring
        _ ≤ 3 * 1 := by gcongr <;> exact h_squares
        _ = 3 := by ring
    exact h_main
