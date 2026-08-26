import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction n with
  | zero => norm_num
  | succ n IH =>
  rw [Finset.sum_range_succ]
  rw [IH]
  have h1 : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by rw [Nat.factorial_succ]
  have h2 : Nat.factorial (n + 2) - 1 = Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1) - 1 := by
    rw [h1]; ring
  rw [h2]
  have h3 : Nat.factorial (n + 1) ≥ 1 := Nat.factorial_pos _
  omega

lemma factorial_succ_eq (n : ℕ) :
    Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by aesop

/-- Helper: empty sum equals zero -/
lemma sum_empty_is_zero :
    ∑ i ∈ Finset.range 0, (i + 1) * Nat.factorial (i + 1) = 0 := by norm_num

/-- Helper: sum range split -/
lemma sum_range_split (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (i + 1) * Nat.factorial (i + 1) = 
      (∑ i ∈ Finset.range k, (i + 1) * Nat.factorial (i + 1)) + (k + 1) * Nat.factorial (k + 1) := by
  simp [Finset.sum_range_succ, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
  <;> ring
  <;> simp_all [Nat.factorial_succ]

/-- Helper: factorial growth ensures subtraction is valid -/
lemma fact_ge_one (n : ℕ) :
    Nat.factorial (n + 1) ≥ 1 := by exact Nat.factorial_pos _

/-- Helper: convert factorial product to next factorial -/
lemma mult_factorial_eq_next_fact (n : ℕ) :
    (n + 1) * Nat.factorial (n + 1) = Nat.factorial (n + 2) - Nat.factorial (n + 1) := by
  have h : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by
    rw [Nat.factorial_succ]
  have h2 : (n + 2) * Nat.factorial (n + 1) = (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) := by
    ring
  have h3 : Nat.factorial (n + 2) - Nat.factorial (n + 1) = (n + 1) * Nat.factorial (n + 1) := by
    rw [h, h2]
    have h4 : Nat.factorial (n + 1) ≥ 1 := Nat.factorial_pos _
    omega
  rw [h3]
  <;> ring

/-- Helper: natural number subtraction when subtracting from larger value -/
lemma nat_sub_cancel (a b : ℕ) (h : b ≤ a) :
    a - b + b = a := by
  rw [Nat.sub_add_cancel h]

/-- Helper: factorial strictly increases for n ≥ 0 -/
lemma fact_strictly_increasing (n : ℕ) :
    Nat.factorial (n + 1) > 0 := by
  exact Nat.factorial_pos _

/-- Main inductive helper -/
lemma sumfact_inductive_step (n : ℕ) (IH : ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) = Nat.factorial (n + 1) - 1) :
    ∑ i ∈ Finset.range (n + 1), (i + 1) * Nat.factorial (i + 1) = Nat.factorial (n + 2) - 1 := by
  exact?

/-- Base case for induction -/
lemma sumfact_base_case :
    ∑ i ∈ Finset.range 0, (i + 1) * Nat.factorial (i + 1) = Nat.factorial 1 - 1 := by
  norm_num
