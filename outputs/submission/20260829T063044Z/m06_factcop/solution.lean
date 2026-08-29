import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  sorry

-- Helper lemmas (stated with `by linarith` as per skeleton requirements)

lemma dvd_gcd_of_dvd_both {a b d : ℕ} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ Nat.gcd a b := by
  exact?

/-- If `d` divides both `a` and `b`, then `d` divides any linear combination `x * a + y * b`. -/
lemma dvd_linear_combination {a b d x y : ℕ} (h : d ∣ a) (h' : d ∣ b) :
    d ∣ x * a + y * b := by
  exact?

/-- `(n+1)! = (n+1) * n!`. -/
lemma factorial_succ_eq (n : ℕ) :
    Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
  aesop

/-- If `d` divides `n` and `1 ≤ n`, then `d ≤ n`. -/
lemma dvd_le_of_pos {n d : ℕ} (hd : d ∣ n) (hn : 1 ≤ n) : d ≤ n := by
  exact?

/-- If `d` divides `a` and `a+1`, then `d` divides `1`. -/
lemma dvd_consecutive_implies_one {a d : ℕ} (h1 : d ∣ a) (h2 : d ∣ a + 1) : d ∣ 1 := by
  exact?

/-- If `d` divides `1`, then `d = 1`. -/
lemma dvd_one_implies_eq_one {d : ℕ} (hd : d ∣ 1) : d = 1 := by
  simp_all
