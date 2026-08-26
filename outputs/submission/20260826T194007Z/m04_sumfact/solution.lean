import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by sorry

-- Pre-existing helper lemmas from challenge file
lemma m04_factorial_succ (n : ℕ) : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by aesop

/-- Helper: base case of the sum (n = 0) -/
lemma m04_sumfact_base : ∑ i ∈ Finset.range 0, (i + 1) * Nat.factorial (i + 1) =
    Nat.factorial (0 + 1) - 1 := by norm_num

/-- Helper: algebraic identity relating factorials -/
lemma m04_fact_identity (n : ℕ) : 
    (n + 1).factorial + (n + 1) * (n + 1).factorial = (n + 2).factorial := by calc
      (n + 1).factorial + (n + 1) * (n + 1).factorial
        = (1 + (n + 1)) * (n + 1).factorial := by ring
      _ = (n + 2) * (n + 1).factorial := by ring
      _ = (n + 2).factorial := by rw [← Nat.factorial_succ]

/-- Helper: convert factorial inequality to ℤ -/
lemma m04_fact_ge_one (n : ℕ) : (1 : ℤ) ≤ ↑(n + 1).factorial := by induction n with
| zero => norm_num [Nat.factorial]
| succ n ih =>
  simp_all [Nat.factorial_succ, mul_add, Nat.cast_add, Nat.cast_mul]
  nlinarith

/-- Helper: convert factorial inequality to ℤ -/
lemma m04_fact_ge_two (n : ℕ) : (1 : ℤ) ≤ ↑(n + 2).factorial := by exact?
