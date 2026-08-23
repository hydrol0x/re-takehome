import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

-- Helper lemmas for the proof

lemma p10_base : Nat.factorial 7 ≥ 3 ^ 7 := by norm_num

lemma p10_step : ∀ n, n ≥ 7 → Nat.factorial n ≥ 3 ^ n → Nat.factorial (n + 1) ≥ 3 ^ (n + 1) := by
  intro n hn hfact
  calc
    Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by simp [Nat.factorial_succ]
    _ ≥ (n + 1) * 3 ^ n := by gcongr
    _ ≥ 3 * 3 ^ n := by
      have : n + 1 ≥ 3 := by omega
      exact Nat.mul_le_mul_right (3 ^ n) this
    _ = 3 ^ (n + 1) := by ring

lemma p10_all_ge_7 : ∀ n, n ≥ 7 → Nat.factorial n ≥ 3 ^ n := by
  intro n hn
  have : ∀ m, m ≥ 7 → Nat.factorial m ≥ 3 ^ m := by
    intro m hm
    induction' hm with m hm ih
    · exact p10_base
    · exact p10_step m ‹m ≥ 7› ‹Nat.factorial m ≥ 3 ^ m›
  exact this n hn

lemma p10_member : Nat.factorial p10_answer < 3 ^ p10_answer := by
  norm_num [p10_answer]

lemma p10_nonmember_gt_6 : ∀ n, n > 6 → Nat.factorial n ≥ 3 ^ n := by
  exact?

/-- The definition of IsGreatest decomposition -/
lemma p10_is_greatest_def : 
    (p10_answer ∈ {n : ℕ | Nat.factorial n < 3 ^ n}) ∧ 
    (∀ n, n ∈ {n : ℕ | Nat.factorial n < 3 ^ n} → n ≤ p10_answer) := by
  refine ⟨p10_member, fun n hn => ?_⟩
  simp only [Set.mem_setOf_eq] at hn
  by_cases h : n ≤ 6
  · exact h
  · have : n ≥ 7 := by omega
    have hfact : Nat.factorial n ≥ 3 ^ n := p10_all_ge_7 n ‹n ≥ 7›
    linarith

/-- Main theorem statement -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  exact p10_is_greatest_def
