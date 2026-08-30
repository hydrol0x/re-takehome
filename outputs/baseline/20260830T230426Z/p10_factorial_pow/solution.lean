import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- membership of 6
  have hmem : Nat.factorial 6 < 3 ^ 6 := by
    norm_num
  refine ⟨hmem, ?_⟩
  intro n hn
  -- we prove by contradiction that `n ≤ 6`
  by_contra hnot
  have hgt : 6 < n := Nat.lt_of_not_ge hnot
  have hseven : 7 ≤ n := Nat.succ_le_of_lt hgt
  -- auxiliary lemma: for all `m ≥ 7`, `3 ^ m ≤ m!`
  have h_pow_fact : ∀ m, 7 ≤ m → 3 ^ m ≤ Nat.factorial m := by
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    -- now goal: `3 ^ (7 + k) ≤ (7 + k)!`
    induction k with
    | zero =>
        simpa using (by norm_num : (3 ^ 7 : ℕ) ≤ 7!)
    | succ k ih =>
        -- we have `3 ^ (7 + k.succ) ≤ (7 + k.succ)!`
        have h3le : (3 : ℕ) ≤ 7 + k.succ := by
          have h8le : (8 : ℕ) ≤ 7 + k.succ := by
            have : (7 : ℕ) ≤ 7 + k := Nat.le_add_right _ _
            have : (8 : ℕ) ≤ (7 + k).succ := Nat.succ_le_succ this
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
          exact le_trans (by decide) h8le
        calc
          3 ^ (7 + k.succ) = 3 ^ ((7 + k) + 1) := by
            simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          _ = 3 * 3 ^ (7 + k) := by
            simpa [Nat.pow_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          _ ≤ (7 + k.succ) * 3 ^ (7 + k) := by
            exact Nat.mul_le_mul_left _ h3le
          _ ≤ (7 + k.succ) * Nat.factorial (7 + k) := by
            exact Nat.mul_le_mul_left _ ih
          _ = Nat.factorial (7 + k.succ) := by
            simpa [Nat.factorial_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hle' : 3 ^ n ≤ Nat.factorial n := h_pow_fact n hseven
  have : Nat.factorial n < Nat.factorial n := lt_of_lt_of_le hn hle'
  exact lt_irrefl _ this
