import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

lemma base_case : Nat.factorial 6 < 3 ^ 6 := by norm_num

/-- For $k \geq 7$, if $k! \geq 3^k$ then $(k+1)! \geq 3^{k+1}$ -/
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

/-- Computation that $7! \ge 3^7$. -/
lemma factorial_7_ge : Nat.factorial 7 ≥ 3 ^ 7 := by norm_num

/-- For all $n \ge 7$, we have $n! \ge 3^n$. -/
lemma all_ge_7 : ∀ n, n ≥ 7 → Nat.factorial n ≥ 3 ^ n := by
  intro n hn
  have base : Nat.factorial 7 ≥ 3 ^ 7 := factorial_7_ge
  have step :
      ∀ m, 7 ≤ m → Nat.factorial m ≥ 3 ^ m →
        Nat.factorial (m + 1) ≥ 3 ^ (m + 1) := by
    intro m hm hmge
    exact induction_step hm hmge
  exact Nat.le_induction base step n hn

/-- Any $n > 6$ satisfies $n! \ge 3^n$. -/
lemma gt_satisfies (n : ℕ) (h : p10_answer < n) : Nat.factorial n ≥ 3 ^ n := by
  have h7 : 7 ≤ n := Nat.succ_le_of_lt h
  exact all_ge_7 n h7

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  refine ⟨?mem, ?ub⟩
  · -- membership
    simpa [p10_answer] using base_case
  · -- upper bound: any element of the set is ≤ p10_answer
    intro n hn
    by_contra hle
    have hlt : p10_answer < n := Nat.lt_of_not_ge hle
    have hge : Nat.factorial n ≥ 3 ^ n := gt_satisfies n hlt
    have hcontr : Nat.factorial n < Nat.factorial n := lt_of_lt_of_le hn hge
    exact lt_irrefl _ hcontr
