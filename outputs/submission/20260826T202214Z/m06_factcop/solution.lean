import Mathlib

-- Helper 1: Expand (n+1)*(n!+1) to relate to (n+1)!
lemma factorial_mul_expansion (n : ℕ) :
    (n + 1) * (Nat.factorial n + 1) = Nat.factorial (n + 1) + n + 1 := by
  aesop

-- Helper 2: Establish the inequality required for subtraction in ℕ
lemma factorial_sub_inequality (n : ℕ) :
    Nat.factorial (n + 1) + 1 ≤ (n + 1) * (Nat.factorial n + 1) := by
  norm_num [Nat.factorial]

-- Helper 3: Compute the difference exactly
lemma factorial_difference (n : ℕ) :
    (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) = n := by
  induction n with
  | zero => norm_num [Nat.factorial]
  | succ n ih =>
    simp [Nat.factorial_succ, mul_add, add_mul, Nat.mul_succ]
    ring_nf at *
    omega

-- Helper 4: n divides n! for n ≥ 1
lemma n_dvd_factorial (n : ℕ) (hn : 1 ≤ n) :
    n ∣ Nat.factorial n := by
  -- Proof 1: Induction on the inequality hypothesis using le_induction
  induction' hn with k hk IH
  · simp [Nat.factorial]
  · rw [Nat.factorial_succ]
    exact dvd_mul_right _ _

-- Helper 5: Any common divisor of n!+1 and (n+1)!+1 divides n
lemma common_divisor_dvd_n (n : ℕ) (hn : 1 ≤ n) {d : ℕ}
    (hA : d ∣ Nat.factorial n + 1) (hB : d ∣ Nat.factorial (n + 1) + 1) :
    d ∣ n := by
  sorry

-- Helper 6: If d divides 1, then d = 1
lemma dvd_one_implies_eq_one (d : ℕ) (hd : d ∣ 1) :
    d = 1 := by
  simp_all

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  sorry
