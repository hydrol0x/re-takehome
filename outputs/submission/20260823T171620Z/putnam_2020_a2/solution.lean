import Mathlib

abbrev putnam_2020_a2_solution : ℕ → ℕ := fun k => 4 ^ k

theorem putnam_2020_a2
  (k : ℕ) :
  (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) =
    putnam_2020_a2_solution k := by sorry

-- Helper lemmas below

lemma base_case : 
  (∑ j ∈ Finset.Icc 0 0, 2 ^ (0 - j) * Nat.choose (0 + j) j) = 4 ^ 0 := by norm_num

lemma helper_sum_shift (k j : ℕ) (h : j ≤ k) : 
  2 ^ (k - j) * Nat.choose (k + j) j = 2 ^ (k - j) * Nat.choose (k + j) (k + j - j) := by rw [Nat.choose_symm] <;> simp_all [add_comm]

lemma helper_choose_symmetry (n m : ℕ) (h : m ≤ n) : 
  Nat.choose n m = Nat.choose n (n - m) := by simp_all

lemma helper_sum_bound (k : ℕ) : 
  ∃ (S : ℕ), (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = S ∧ S = 4 ^ k := by sorry

lemma helper_induction_step (k : ℕ) 
  (h : ∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j = 4 ^ k) :
  ∑ j ∈ Finset.Icc 0 (k + 1), 2 ^ ((k + 1) - j) * Nat.choose ((k + 1) + j) j = 4 ^ (k + 1) := by exact?

lemma helper_finite_sum_eq (k : ℕ) : 
  (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k := by exact?
