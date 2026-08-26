import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- first, show that 6 belongs to the set
  have h_mem : Nat.factorial p10_answer < 3 ^ p10_answer := by
    simpa [p10_answer] using (by norm_num : Nat.factorial 6 < 3 ^ 6)
  -- a lemma: for every `n ≥ 7` we have `3 ^ n ≤ n!`
  have h_pow_le_fact : ∀ n, 7 ≤ n → 3 ^ n ≤ Nat.factorial n := by
    intro n hn
    rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
    -- now we need `∀ k, 3 ^ (7 + k) ≤ (7 + k)!`
    have : ∀ k, 3 ^ (7 + k) ≤ Nat.factorial (7 + k) := by
      intro k
      induction k with
      | zero =>
          norm_num
      | succ k ih =>
          have h3 : 3 ≤ 7 + k + 1 := by omega
          calc
            3 ^ (7 + k + 1)
                = 3 ^ (7 + k) * 3 := by
                  simpa [Nat.pow_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using rfl
            _ = 3 * 3 ^ (7 + k) := by
                  simp [Nat.mul_comm]
            _ ≤ 3 * Nat.factorial (7 + k) := by
                  exact Nat.mul_le_mul_left _ ih
            _ ≤ (7 + k + 1) * Nat.factorial (7 + k) := by
                  exact Nat.mul_le_mul_right _ h3
            _ = Nat.factorial (7 + k + 1) := by
                  simpa [Nat.factorial_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using rfl
    exact this k
  refine ⟨?mem, ?bound⟩
  · -- membership
    exact h_mem
  · -- maximality
    intro n hn
    by_contra hle
    have h7 : 7 ≤ n := by
      have h6lt : 6 < n := Nat.lt_of_not_ge hle
      exact Nat.succ_le_of_lt h6lt
    have hpowle : 3 ^ n ≤ Nat.factorial n := h_pow_le_fact n h7
    exact (not_lt_of_ge hpowle) hn
