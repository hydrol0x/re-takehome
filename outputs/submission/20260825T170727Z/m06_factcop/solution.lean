import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry

-- Helper lemmas below

lemma factorial_succ_eq (n : ℕ) : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by sorry

lemma fact_plus_one_minus_fact (n : ℕ) : (Nat.factorial n + 1) - Nat.factorial n = 1 := by sorry

lemma nat_le_of_dvd_of_pos {a b : ℕ} (h : b ∣ a) (ha : 0 < a) : b ≤ a := by sorry

lemma dvd_of_dvd_mul_add {a b c d : ℕ} (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ c * a + b := by sorry

lemma gcd_eq_one_of_dvd_one {a b : ℕ} (h : ∀ d, d ∣ a → d ∣ b → d ∣ 1) : Nat.gcd a b = 1 := by sorry

lemma dvd_sub_of_dvd_left {a b : ℕ} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := by sorry

lemma one_dvd_any {a : ℕ} : 1 ∣ a := by sorry
