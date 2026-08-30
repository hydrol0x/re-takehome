import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open Finset

theorem rmo_2000_3
  (x : ℕ → ℝ)
  (hpos : ∀ n, 0 < x n)
  (hmono : ∀ n, x n ≥ x (n + 1))
  (hsq : ∀ N, (Ico 1 (N + 1)).sum (fun i => x (i * i) / (i : ℝ)) ≤ 1) :
  ∀ k, (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
  intro k
  let J := Nat.sqrt k
  have hJ_sq : J * J ≤ k := Nat.sqrt_le' k
  have hJ_lt : k < (J + 1) * (J + 1) := Nat.lt_succ_sqrt_mul_self k
  
  -- Helper: x is antitone
  have hx_antitone : ∀ m n, m ≤ n → x n ≤ x m := by
    intro m n hmn
    have : ∀ p q, p ≤ q → x q ≤ x p := by
      intro p q hpq
      induction' hpq with q hpq IH
      · simp
      · have h := hmono q
        exact IH.trans h
    exact this m n hmn

  cases k with
  | zero =>
    simp [Ico]
    norm_num
  | succ k' =>
    have hJ_pos : 0 < J := by
      rw [← Nat.succ_pred_eq_of_pos hJ_sq]
      exact Nat.pos_iff_ne_zero.mpr (by
        intro h
        rw [h] at hJ_sq
        norm_num at hJ_sq)
        
    -- Split sum at J^2
    have h_sum_split : (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) = 
      (Ico 1 (J * J)).sum (fun i => x i / (i : ℝ)) + (Ico (J * J) (k + 1)).sum (fun i => x i / (i : ℝ)) := by
      rw [← Finset.sum_union]
      · congr 1
        ext i
        simp [Ico, Nat.lt_succ_iff]
        constructor
        · rintro ⟨h₁, h₂⟩
          exact ⟨h₁, by omega⟩
        · rintro ⟨h₁, h₂⟩
          exact ⟨by omega, h₂⟩
      · simp [Ico, Nat.lt_succ_iff]
        intro i hi
        simp_all [Ico, Nat.lt_succ_iff]
        omega
      · simp [Ico, Nat.lt_succ_iff]
        intro i hi
        simp_all [Ico, Nat.lt_succ_iff]
        omega
        
    -- Bound tail
    have h_tail_bound : (Ico (J * J) (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 
      ((k + 1 - J * J) : ℝ) * (x (J * J) / (J * J : ℝ)) := by
      calc
        _ = (Ico (J * J) (k + 1)).sum (fun i => x i / (i : ℝ)) := rfl
        _ ≤ (Ico (J * J) (k + 1)).sum (fun i => x (J * J) / (J * J : ℝ)) := by
          apply Finset.sum_le_sum
          intro i hi
          have h_ge : (J * J : ℝ) ≤ i := by
            simp [Ico] at hi
            norm_cast
            linarith
          have h_mono_x : x i ≤ x (J * J) := hx_antitone (J * J) i (by exact_mod_cast h_ge)
          have h_inv : (i : ℝ) ≥ (J * J : ℝ) := by exact_mod_cast h_ge
          have h_inv_pos : 0 < (i : ℝ) := by
            simp [Ico] at hi
            norm_cast
            linarith
          have h_inv_le : 1 / (i : ℝ) ≤ 1 / (J * J : ℝ) := by
            apply one_div_le_one_div_of_le
            · positivity
            · exact_mod_cast h_ge
          calc
            x i / (i : ℝ) = x i * (1 / (i : ℝ)) := by ring
            _ ≤ x (J * J) * (1 / (J * J : ℝ)) := by gcongr <;> assumption
            _ = x (J * J) / (J * J : ℝ) := by ring
        _ = ((k + 1 - J * J) : ℝ) * (x (J * J) / (J * J : ℝ)) := by
          simp [Finset.sum_const, Finset.card_range]
          -- Wait, card of Ico (J^2) (k+1) is k+1 - J^2
          -- Finset.card_Ico
          rw [Finset.card_eq_sum_ones]
          simp [Finset.sum_const, Finset.card_Ico]
          norm_cast
          <;> ring_nf
          <;> omega
          
    -- Bound head
    -- Ico 1 (J^2) = Union_{j=1}^{J-1} Ico (j^2) ((j+1)^2)
    -- If J=1, Ico 1 1 is empty.
    have h_head_bound : (Ico 1 (J * J)).sum (fun i => x i / (i : ℝ)) ≤ 
      2 * (∑ j in Ico 1 J, x (j * j) / (j : ℝ)) + (∑ j in Ico 1 J, x (j * j) / (j * j : ℝ)) := by
      -- Decompose Ico 1 (J^2)
      have h_decomp : Ico 1 (J * J) = ⋃ j ∈ Ico 1 J, Ico (j * j) ((j + 1) * (j + 1)) := by
        -- This equality holds for J >= 1
        -- Ico 1 J is {1, ..., J-1}
        -- Union of [j^2, (j+1)^2) for j=1..J-1 is [1, J^2)
        sorry -- Will fill this later
      -- Instead of proving set equality, I can use Finset.sum over Ico 1 J
      -- and sum over each block.
      -- But I need to justify the decomposition.
      -- Let's use `Finset.sum_Union` if disjoint.
      -- The blocks are disjoint.
      -- I'll skip the explicit set equality and just sum over j.
      -- Sum_{i=1}^{J^2-1} f(i) = Sum_{j=1}^{J-1} Sum_{i=j^2}^{(j+1)^2-1} f(i)
      -- This is a known identity for partitions.
      -- I'll use `Finset.sum_Union` with `disjoint_on`.
      sorry
      
    -- Combine bounds
    have h_final : (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
      sorry
      
    exact h_final
