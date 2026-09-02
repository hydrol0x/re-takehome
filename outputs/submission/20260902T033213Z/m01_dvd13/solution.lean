import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction' n with k hk
  · -- Base case: n = 0
    norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Inductive step: assume true for k, prove for k + 1
    rw [show 4 ^ (2 * (k + 1) + 1) = 4 ^ (2 * k + 1 + 2) by ring_nf, 
        show 3 ^ ((k + 1) + 2) = 3 ^ (k + 2 + 1) by ring_nf]
    rw [pow_add, pow_add]
    simp [pow_succ, mul_assoc, mul_comm, mul_left_comm] at hk ⊢
    -- Use omega to complete the divisibility check
    omega