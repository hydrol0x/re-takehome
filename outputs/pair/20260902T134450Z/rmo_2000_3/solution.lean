import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

open Finset

theorem rmo_2000_3
  (x : ℕ → ℝ)
  (hpos : ∀ n, 0 < x n)
  (hmono : ∀ n, x n ≥ x (n + 1))
  (hsq : ∀ N, (Ico 1 (N + 1)).sum (fun i => x (i * i) / (i : ℝ)) ≤ 1) :
  ∀ k, (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
  intro k
  cases k with
  | zero =>
    simp
  | succ k' =>
    let M := Nat.sqrt (k' + 1)
    have hM_sq_le : M * M ≤ k' + 1 := Nat.sqrt_le' (k' + 1)
    have hM_lt : k' + 1 < (M + 1) * (M + 1) := Nat.lt_succ_sqrt_mul_self (k' + 1)
    have hM_pos : 0 < M := by
      apply Nat.pos_of_ne_zero
      intro h
      rw [h] at hM_sq_le
      norm_num at hM_sq_le
      linarith
    -- Now I need to split the sum
    have h_sum_split : (Ico 1 (k' + 1 + 1)).sum (fun i => x i / (i : ℝ)) = 
      (∑ m in Ico 1 (M + 1), ∑ i in Ico (m * m) (min (k' + 1 + 1) ((m + 1) * (m + 1))), x i / (i : ℝ)) := by sorry
    sorry
