import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

-- Helper: Compute Legendre's formula for v₃(100!)
lemma legendre_v3_100_eq_48 :
    (Finset.sum (Finset.range 5) fun i => 100 / 3 ^ (i + 1)) = 48 := by
  rfl

-- Helper: If 3^k divides 100! then k ≤ 48
lemma v3_factorial_100_upper_bound :
    ∀ k : ℕ, 3 ^ k ∣ Nat.factorial 100 → k ≤ 48 := by
  intro k hk
  by_contra h
  -- If k > 48, then k ≥ 49
  have h₁ : k ≥ 49 := by omega
  -- But 3^49 does not divide 100!
  have h₂ : ¬(3 ^ 49 ∣ Nat.factorial 100) := by norm_num
  have h₃ : 3 ^ k ∣ Nat.factorial 100 := hk
  have h₄ : 3 ^ 49 ∣ Nat.factorial 100 := by
    exact dvd_trans (pow_dvd_pow _ (by omega)) h₃
  exact h₂ h₄

-- Helper: 3^48 divides 100!
lemma three_pow_48_divides_factorial_100 :
    3 ^ 48 ∣ Nat.factorial 100 := by norm_num

-- Helper: 3^49 does not divide 100!
lemma three_pow_49_not_divides_factorial_100 :
    ¬(3 ^ 49 ∣ Nat.factorial 100) := by norm_num

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  refine' ⟨_, _⟩
  · -- First component: h01_answer ∈ {k : ℕ | 3 ^ k ∣ Nat.factorial 100}
    rw [Set.mem_setOf_eq]
    exact three_pow_48_divides_factorial_100
  · -- Second component: for all k, if 3^k ∣ 100! then k ≤ h01_answer
    intro k hk
    have h₁ : k ≤ 48 := v3_factorial_100_upper_bound k hk
    simpa [h01_answer] using h₁
