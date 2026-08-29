import Mathlib

lemma induction_step {k : ℕ} (hk : k ≥ 7) (h : Nat.factorial k ≥ 3 ^ k) : 
    Nat.factorial (k + 1) ≥ 3 ^ (k + 1) := by
  calc
    Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by
      simpa [Nat.succ_eq_add_one] using Nat.factorial_succ k
    _ ≥ (k + 1) * 3 ^ k := by
      exact Nat.mul_le_mul_left (k + 1) h
    _ ≥ 3 ^ (k + 1) := by
      have h' : 3 * 3 ^ k ≤ (k + 1) * 3 ^ k := Nat.mul_le_mul_right (3 ^ k) (by omega)
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h'

lemma base_at_seven : Nat.factorial 7 ≥ 3 ^ 7 := by
  norm_num

lemma all_ge_seven_property : ∀ n ≥ 7, Nat.factorial n ≥ 3 ^ n := by
  intro n hn
  set m := n - 7
  have : n = 7 + m := by rw [← Nat.add_sub_cancel_left 7 m]; omega
  rw [this]
  induction m with
  | zero => exact base_at_seven
  | succ m ih =>
    have hk : 7 + m ≥ 7 := by omega
    exact induction_step hk ih

lemma all_gt_six_property : ∀ n > 6, Nat.factorial n ≥ 3 ^ n := by
  intro n hn
  have h_ge_7 : n ≥ 7 := by omega
  exact all_ge_seven_property n h_ge_7

lemma six_in_set : Nat.factorial 6 < 3 ^ 6 := by
  norm_num

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

lemma any_larger_not_in_set : ∀ n > p10_answer, ¬(Nat.factorial n < 3 ^ n) := by
  intro n hn
  have h_ge_7 : n ≥ 7 := by
    simp only [p10_answer] at hn
    omega
  have h_main : Nat.factorial n ≥ 3 ^ n := all_gt_six_property n hn
  omega

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Prove p10_answer ∈ S
    rw [p10_answer]
    exact six_in_set
  · -- Prove ∀ b ∈ S, b ≤ p10_answer
    intro b hb
    by_contra h
    -- Assume b > p10_answer
    have h_gt : b > p10_answer := by omega
    -- Use the property that larger numbers are not in the set
    have h_not_in : ¬(Nat.factorial b < 3 ^ b) := any_larger_not_in_set b h_gt
    -- Contradiction with membership
    exact h_not_in hb
