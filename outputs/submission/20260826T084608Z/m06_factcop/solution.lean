import Mathlib

/-- Helper: For any n, (n+1)*n! = (n+1)! -/
lemma fact_succ_eq (n : ℕ) : (n + 1) * Nat.factorial n = Nat.factorial (n + 1) := by
  rw [Nat.factorial_succ]
  <;> ring

/-- Helper: For any n ≥ 1, (n+1)*(n!+1) - ((n+1)!+1) = n -/
lemma factcop_subtract (n : ℕ) (hn : 1 ≤ n) : 
    (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) = n := by
  have h1 : (n + 1) * (Nat.factorial n + 1) = (n + 1) * Nat.factorial n + (n + 1) := by
    ring
  rw [h1]
  have h2 : (n + 1) * Nat.factorial n = Nat.factorial (n + 1) := fact_succ_eq n
  rw [h2]
  have h3 : Nat.factorial (n + 1) + (n + 1) - (Nat.factorial (n + 1) + 1) = n := by
    have h4 : 1 ≤ n + 1 := by linarith
    have h5 : Nat.factorial (n + 1) + 1 > 0 := by positivity
    have h6 : Nat.factorial (n + 1) + (n + 1) ≥ Nat.factorial (n + 1) + 1 := by
      omega
    omega
  omega

/-- Helper: If d divides both a and b, then d divides a*n - b for any n -/
lemma dvd_sub_mul {a b d : ℕ} (ha : d ∣ a) (hb : d ∣ b) (n : ℕ) : d ∣ a * n - b := by sorry

/-- Helper: For n ≥ 1, n divides n! -/
lemma n_dvd_factorial (n : ℕ) (hn : 1 ≤ n) : n ∣ Nat.factorial n := by cases n with
| zero => linarith
| succ m => rw [Nat.factorial_succ]; exact dvd_mul_right _ _

/-- Main helper: If d divides both n!+1 and (n+1)!+1, then d divides 1 -/
lemma factcop_common_divisor (n : ℕ) (hn : 1 ≤ n) (d : ℕ) 
    (hd1 : d ∣ Nat.factorial n + 1) (hd2 : d ∣ Nat.factorial (n + 1) + 1) : 
    d ∣ 1 := by sorry

/-- Main theorem: For every n ≥ 1, n!+1 and (n+1)!+1 are coprime -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry
