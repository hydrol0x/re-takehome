import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h_factorial_ge_one : ∀ k : ℕ, 1 ≤ Nat.factorial (k + 1) := by
    intro k
    have h : 0 < Nat.factorial (k + 1) := by
      positivity
    exact Nat.succ_le_of_lt h
  
  -- Base case: n = 0
  have h_base : ∑ i ∈ Finset.range 0, (i + 1) * Nat.factorial (i + 1) = Nat.factorial (0 + 1) - 1 := by
    simp [Finset.sum_range_zero]
    <;> norm_num [Nat.factorial]
  
  -- Inductive step
  have h_inductive_step : ∀ n : ℕ, 
    (∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) = Nat.factorial (n + 1) - 1) →
    (∑ i ∈ Finset.range (n + 1), (i + 1) * Nat.factorial (i + 1) = Nat.factorial (n + 2) - 1) := by
    intro n ih
    have h_sum_range_succ : ∑ i ∈ Finset.range (n + 1), (i + 1) * Nat.factorial (i + 1) =
      ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) + (n + 1) * Nat.factorial (n + 1) := by
      rw [Finset.sum_range_succ]
      <;> simp
    rw [h_sum_range_succ]
    rw [ih]
    have h_fact_ge_one_n1 : 1 ≤ Nat.factorial (n + 1) := h_factorial_ge_one n
    have h_fact_ge_one_n2 : 1 ≤ Nat.factorial (n + 2) := h_factorial_ge_one (n + 1)
    have h_main : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = Nat.factorial (n + 2) - 1 := by
      have h_add : (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) = (n + 2) * Nat.factorial (n + 1) := by
        ring
      have h_fact_succ : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by
        rw [Nat.factorial]
        <;> ring
      have h_left : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = (n + 1) * Nat.factorial (n + 1) + (Nat.factorial (n + 1) - 1) := by
        omega
      calc
        Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1)
          = (n + 1) * Nat.factorial (n + 1) + (Nat.factorial (n + 1) - 1) := by omega
        _ = ((n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1)) - 1 := by
          have h_sub : Nat.factorial (n + 1) ≥ 1 := h_fact_ge_one_n1
          omega
        _ = (n + 2) * Nat.factorial (n + 1) - 1 := by
          rw [h_add]
        _ = Nat.factorial (n + 2) - 1 := by
          rw [h_fact_succ]
    rw [h_main]
  
  -- Main proof by induction
  refine Nat.recOn n ?_ ?_
  · -- Base case
    exact h_base
  · -- Inductive step
    exact h_inductive_step

-- Helper lemmas below for reference (already proven above via inlining)
lemma factorial_pos (k : ℕ) : 0 < Nat.factorial (k + 1) := by
  positivity

lemma factorial_ge_one (k : ℕ) : 1 ≤ Nat.factorial (k + 1) := by
  exact Nat.succ_le_of_lt (factorial_pos k)

lemma sum_range_succ (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i + 1) * Nat.factorial (i + 1) =
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) + (n + 1) * Nat.factorial (n + 1) := by
  rw [Finset.sum_range_succ]
  <;> simp [Nat.add_assoc]

lemma factorial_succ_eq (n : ℕ) :
    Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by
  rw [Nat.factorial]
  <;> ring

lemma add_factorial_identity (n : ℕ) :
    (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) = (n + 2) * Nat.factorial (n + 1) := by
  have h : (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) = ((n + 1) + 1) * Nat.factorial (n + 1) := by
    ring
  rw [h]
  <;> simp [Nat.add_comm]
  <;> ring

lemma factorial_subtract_one_le (n : ℕ) : 1 ≤ Nat.factorial (n + 1) := by
  apply factorial_ge_one

lemma sum_base_case : 
    ∑ i ∈ Finset.range 0, (i + 1) * Nat.factorial (i + 1) = 0 := by
  simp [Finset.sum_range_zero]

lemma factorial_base_case : Nat.factorial (0 + 1) - 1 = 0 := by
  norm_num [Nat.factorial]
