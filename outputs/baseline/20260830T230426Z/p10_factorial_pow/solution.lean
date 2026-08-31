import Mathlib
open Nat

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- membership of `6`
  have hmem6 : Nat.factorial 6 < 3 ^ 6 := by
    norm_num
  have hmem : p10_answer ∈ {n : ℕ | Nat.factorial n < 3 ^ n} := by
    simpa [p10_answer] using hmem6
  refine ⟨hmem, ?_⟩
  -- auxiliary lemma: for `n ≥ 7` we have `3 ^ n ≤ n!`
  have h_pow_le_fact : ∀ n, 7 ≤ n → 3 ^ n ≤ Nat.factorial n := by
    intro n hn
    rcases Nat.le.dest hn with ⟨k, rfl⟩
    -- prove by induction on `k`
    have : ∀ k : ℕ, 3 ^ (7 + k) ≤ Nat.factorial (7 + k) := by
      intro k
      induction k with
      | zero =>
          norm_num
      | succ k ih =>
          have h3le : (3 : ℕ) ≤ 7 + k + 1 := by omega
          have h_left : 3 * 3 ^ (7 + k) ≤ (7 + k + 1) * 3 ^ (7 + k) :=
            Nat.mul_le_mul_right _ h3le
          have h_right : (7 + k + 1) * 3 ^ (7 + k) ≤ (7 + k + 1) * Nat.factorial (7 + k) :=
            Nat.mul_le_mul_left _ ih
          have : 3 * 3 ^ (7 + k) ≤ (7 + k + 1) * Nat.factorial (7 + k) :=
            le_trans h_left h_right
          simpa [pow_succ, Nat.factorial_succ, Nat.add_comm, Nat.add_left_comm,
                 Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    exact this k
  -- now prove the upper‑bound property
  intro n hn
  by_contra hgt
  have hlt : 6 < n := Nat.lt_of_not_ge hgt
  have hseven : 7 ≤ n := Nat.succ_le_of_lt hlt
  have hle : 3 ^ n ≤ Nat.factorial n := h_pow_le_fact n hseven
  have : Nat.factorial n < Nat.factorial n :=
    lt_of_lt_of_le hn hle
  exact lt_irrefl _ this
