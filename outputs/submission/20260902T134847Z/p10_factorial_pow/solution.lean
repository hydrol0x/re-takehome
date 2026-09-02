import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- Helper: 6! < 3^6 -/
lemma fact_6_lt_pow_6 : Nat.factorial 6 < 3 ^ 6 := by norm_num

/-- Helper: 7! ≥ 3^7 -/
lemma fact_7_ge_pow_7 : Nat.factorial 7 ≥ 3 ^ 7 := by norm_num

/-- Helper: if k ≥ 7 and k! ≥ 3^k, then (k+1)! ≥ 3^(k+1) -/
lemma factorial_inductive_step (k : ℕ) (hk : k ≥ 7) (h : Nat.factorial k ≥ 3 ^ k) :
    Nat.factorial (k + 1) ≥ 3 ^ (k + 1) := by calc
      Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by simp [Nat.factorial_succ]
      _ ≥ (k + 1) * 3 ^ k := Nat.mul_le_mul_left _ h
      _ ≥ 3 * 3 ^ k := by
        have : k + 1 ≥ 3 := by omega
        exact Nat.mul_le_mul_right _ this
      _ = 3 ^ (k + 1) := by ring

/-- Helper: for all n ≥ 7, n! ≥ 3^n -/
lemma factorial_ge_pow_for_n_ge_7 (n : ℕ) (h : n ≥ 7) : Nat.factorial n ≥ 3 ^ n := by refine Nat.le_induction fact_7_ge_pow_7 factorial_inductive_step n h

/-- If n > 6, then n! ≥ 3^n -/
lemma n_gt_6_implies_fact_ge_pow (n : ℕ) (h : n > 6) : Nat.factorial n ≥ 3 ^ n := by
  have h' : n ≥ 7 := by omega
  exact factorial_ge_pow_for_n_ge_7 n h'

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- p10_answer ∈ {n : ℕ | n! < 3^n}
    rw [Set.mem_setOf_eq]
    rw [p10_answer]
    exact fact_6_lt_pow_6
  · -- ∀ n ∈ {n : ℕ | n! < 3^n}, n ≤ p10_answer
    intro n hn
    rw [Set.mem_setOf_eq] at hn
    by_contra h
    -- Assume n > p10_answer, derive contradiction
    have h' : n > p10_answer := by omega
    have h'' : Nat.factorial n ≥ 3 ^ n := n_gt_6_implies_fact_ge_pow n h'
    -- But we also have n! < 3^n from hn
    have h''' : Nat.factorial n < 3 ^ n := hn
    linarith
