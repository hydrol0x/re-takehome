import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

-- Helper Lemma 1: Membership verification for p10_answer
lemma p10_helper_membership : Nat.factorial 6 < 3 ^ 6 := by norm_num

-- Helper Lemma 2: Base case for induction (n = 7)
lemma p10_helper_base_ge_pow : Nat.factorial 7 ≥ 3 ^ 7 := by norm_num

-- Helper Lemma 3: Inductive step for n ≥ 7
lemma p10_helper_step_ge_pow : ∀ k, k ≥ 7 → Nat.factorial k ≥ 3 ^ k → Nat.factorial (k + 1) ≥ 3 ^ (k + 1) := by sorry

-- Helper Lemma 4: Proves n! ≥ 3^n for all n ≥ 7
lemma p10_helper_induction_ge_pow : ∀ n, 7 ≤ n → Nat.factorial n ≥ 3 ^ n := by sorry

-- Helper Lemma 5: Upper bound property (n! < 3^n implies n ≤ 6)
lemma p10_helper_upper_bound (n : ℕ) (h : Nat.factorial n < 3 ^ n) : n ≤ p10_answer := by sorry

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Show p10_answer ∈ S (Membership)
    rw [Set.mem_setOf_eq]
    exact p10_helper_membership
  · -- Show ∀ n ∈ S, n ≤ p10_answer (Upper Bound)
    intro n hn
    exact p10_helper_upper_bound n hn
