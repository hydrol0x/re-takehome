import Mathlib

/-- Helper: `(n+1) * (n! + 1) = (n+1)! + (n+1)` -/
lemma helper_eq1 (n : ℕ) :
    (n + 1) * (Nat.factorial n + 1) = Nat.factorial (n + 1) + (n + 1) := by aesop

/-- Helper: `n = (n+1)*(n!+1) - ((n+1)!+1)` -/
lemma helper_eq2 (n : ℕ) :
    n = (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) := by sorry

/-- Helper: `(n+1)*(n!+1) >= (n+1)!+1` for `n >= 1` -/
lemma helper_ge (n : ℕ) (hn : 1 ≤ n) :
    (n + 1) * (Nat.factorial n + 1) ≥ Nat.factorial (n + 1) + 1 := by norm_num [Nat.factorial]

/-- Helper: `n ∣ n!` for `n >= 1` -/
lemma helper_dvd_fact (n : ℕ) (hn : 1 ≤ n) :
    n ∣ Nat.factorial n := by cases n <;> simp_all [Nat.factorial]

/-- Helper: If `d ∣ n` and `n ∣ n!`, then `d ∣ n!` -/
lemma helper_trans_dvd (n d : ℕ) (hd : d ∣ n) (hn : n ∣ Nat.factorial n) :
    d ∣ Nat.factorial n := by exact?

/-- Helper: If `d ∣ a` and `d ∣ a+1`, then `d ∣ 1` -/
lemma helper_dvd_one (a d : ℕ) (ha : d ∣ a) (ha1 : d ∣ a + 1) :
    d ∣ 1 := by exact?

/-- Helper: For any common divisor `d` of `n!+1` and `(n+1)!+1`, we have `d=1` -/
lemma helper_common_divisor_is_one (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (hd1 : d ∣ Nat.factorial n + 1) (hd2 : d ∣ Nat.factorial (n + 1) + 1) :
    d = 1 := by sorry

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry
