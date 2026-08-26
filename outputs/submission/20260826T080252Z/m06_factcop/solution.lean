import Mathlib

-- Helper: Key algebraic identity relating (n+1)*(n!+1) and (n+1)!+1
lemma fact_linear_combination (n : ℕ) : (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) = n := by
  calc
    (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1)
      = (n + 1) * (Nat.factorial n + 1) - ((n + 1) * Nat.factorial n + 1) := by rw [Nat.factorial_succ]
    _ = (n + 1) * Nat.factorial n + (n + 1) - ((n + 1) * Nat.factorial n + 1) := by ring
    _ = n := by
      have h : (n + 1) * Nat.factorial n ≤ (n + 1) * Nat.factorial n + (n + 1) := by
        omega
      simp [Nat.add_sub_assoc, Nat.add_sub_cancel_left, Nat.add_comm, Nat.sub_add_cancel]
      <;> omega

-- Helper: For n ≥ 1, n divides n!
lemma nat_le_factorial_dvd (n : ℕ) (hn : 1 ≤ n) : n ∣ Nat.factorial n := by
  cases n with
  | zero => 
      cases (Nat.not_succ_le_self 0 hn)
  | succ n => 
      simpa [Nat.factorial_succ] using Nat.dvd_mul_left (Nat.succ n) (Nat.factorial n)

-- Helper: If d divides a and d divides b, then d divides their difference (when subtraction makes sense)
lemma dvd_sub_of_dvd_left {a b d : ℕ} (h₁ : d ∣ a) (h₂ : d ∣ b) (h₃ : b ≤ a) : d ∣ a - b := by
  exact?

-- Helper: If gcd(a,b) = 1, then a and b are coprime (standard equivalence)
lemma gcd_one_iff_coprime (a b : ℕ) : Nat.gcd a b = 1 ↔ Nat.Coprime a b := by
  norm_num

-- Main theorem
/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  sorry
