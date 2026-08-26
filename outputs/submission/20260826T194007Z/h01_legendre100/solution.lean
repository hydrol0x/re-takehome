import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  have h_main : 3 ^ 48 ∣ Nat.factorial 100 := by
    norm_num [Nat.dvd_factorial]
    <;> decide
  
  have h_upper : ∀ k : ℕ, 3 ^ k ∣ Nat.factorial 100 → k ≤ 48 := by
    intro k hk
    have h_val : 48 = (100 / 3) + (100 / 9) + (100 / 27) + (100 / 81) := by
      norm_num
    -- Use the fact that v_3(100!) = 48 via Legendre's formula
    -- and any k with 3^k | 100! must satisfy k ≤ 48
    have h_bound : k ≤ 48 := by
      by_contra h
      have h_gt : k ≥ 49 := by omega
      have h_pow : 3 ^ 49 ∣ 3 ^ k := by
        apply pow_dvd_pow _
        omega
      have h_div : 3 ^ 49 ∣ Nat.factorial 100 := dvd_trans h_pow hk
      norm_num [h_val] at h_div
      <;> simp_all [Nat.dvd_factorial]
      <;> norm_num
      <;> omega
    exact h_bound
  constructor
  · exact h_main
  · intro k hk
    exact h_upper k hk
