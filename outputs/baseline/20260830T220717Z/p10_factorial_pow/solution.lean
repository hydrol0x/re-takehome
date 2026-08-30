import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  refine ⟨?mem, ?bound⟩
  · -- membership of the answer
    have : Nat.factorial 6 < 3 ^ 6 := by norm_num
    simpa using this
  · -- any element of the set is ≤ 6
    intro n hn
    by_contra hle
    have hlt : 6 < n := Nat.lt_of_not_ge hle
    have h7 : 7 ≤ n := Nat.succ_le_of_lt hlt
    -- prove factorial n ≥ 3 ^ n for n ≥ 7
    have hge : Nat.factorial n ≥ 3 ^ n := by
      -- base case at 7
      have base : Nat.factorial 7 ≥ 3 ^ 7 := by norm_num
      -- inductive step
      have step :
          ∀ {k}, 7 ≤ k → Nat.factorial k ≥ 3 ^ k →
            Nat.factorial (k + 1) ≥ 3 ^ (k + 1) := by
        intro k hk hkineq
        have h_mul : (k + 1) * Nat.factorial k ≥ (k + 1) * 3 ^ k :=
          Nat.mul_le_mul_left _ hkineq
        have h3le : (3 : ℕ) ≤ k + 1 := by
          have : (7 : ℕ) ≤ k + 1 := Nat.succ_le_succ hk
          exact Nat.le_trans (by decide) this
        have h_mul2 : (k + 1) * 3 ^ k ≥ 3 * 3 ^ k :=
          Nat.mul_le_mul_right _ h3le
        have : (k + 1) * Nat.factorial k ≥ 3 ^ (k + 1) := by
          calc
            (k + 1) * Nat.factorial k
                ≥ (k + 1) * 3 ^ k := h_mul
            _ ≥ 3 * 3 ^ k := h_mul2
            _ = 3 ^ (k + 1) := by
              simpa [Nat.pow_succ, Nat.mul_comm]
        simpa [Nat.factorial_succ] using this
      exact Nat.le_induction h7 base step
    have : Nat.factorial n < Nat.factorial n := lt_of_lt_of_le hn hge
    exact (lt_irrefl _ this)
