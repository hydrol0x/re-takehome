import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

abbrev putnam_2020_a2_solution : ℕ → ℕ := fun k => 4 ^ k

theorem putnam_2020_a2
  (k : ℕ) :
  (∑ j in Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) =
    putnam_2020_a2_solution k := by
  have h : ∀ k : ℕ, ∑ j in Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j = 4 ^ k := by
    intro k
    induction k with
    | zero =>
      simp [Finset.sum_Icc_succ_top]
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp [Nat.succ_eq_add_one, pow_add, mul_add, mul_comm, mul_left_comm, mul_assoc,
            Nat.choose_succ_succ, Nat.add_sub_cancel] at ih ⊢
      ring_nf at ih ⊢
      omega
  exact h k
