import Mathlib

theorem putnam_2020_a2 (k : ℕ) :
  ∑ j in Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j = 4 ^ k := by
  have h : ∀ n : ℕ, ∑ j in Finset.Icc 0 n, 2 ^ (n - j) * Nat.choose (n + j) j = 4 ^ n := by
    intro n
    induction' n with n ih
    · simp [Finset.sum_range_succ]
    · rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      simp [Nat.pow_succ, Nat.mul_sub_left_distrib, Nat.add_sub_assoc, Nat.sub_add_cancel]
      <;> ring_nf at *
      <;> simp_all [Nat.choose_succ_succ, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
      <;> ring_nf at *
      <;> omega
  exact h k
