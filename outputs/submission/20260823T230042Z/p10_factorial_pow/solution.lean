import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

lemma factorial_6_less_than_3_pow_6 : Nat.factorial 6 < 3 ^ 6 := by
  norm_num [Nat.factorial]

lemma three_pow_le_factorial_ge_7 (n : ℕ) (h : 7 ≤ n) :
    3 ^ n ≤ Nat.factorial n := by
  have h_sub : n = (n - 7) + 7 := by omega
  rw [h_sub]
  induction (n - 7) with
  | zero =>
    norm_num [Nat.factorial]
  | succ m ih =>
    calc
      3 ^ (m + 1 + 7) = 3 * 3 ^ (m + 7) := by ring
      _ ≤ 3 * Nat.factorial (m + 7) := by gcongr
      _ ≤ (m + 1 + 7) * Nat.factorial (m + 7) := by
        gcongr <;> omega
      _ = Nat.factorial (m + 1 + 7) := by
        rw [show m + 1 + 7 = (m + 7) + 1 by ring]
        simp [Nat.factorial]

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Show p10_answer ∈ {n : ℕ | Nat.factorial n < 3 ^ n}
    rw [p10_answer]
    exact factorial_6_less_than_3_pow_6
  · -- Show ∀ m, m ∈ {n : ℕ | Nat.factorial n < 3 ^ n} → m ≤ p10_answer
    intro m hm
    by_contra h
    have h_gt : p10_answer < m := by omega
    rw [p10_answer] at h_gt
    have h_ge_7 : 7 ≤ m := by omega
    have h_ineq : 3 ^ m ≤ Nat.factorial m := 
      three_pow_le_factorial_ge_7 m h_ge_7
    have h_mem : Nat.factorial m < 3 ^ m := hm
    omega
