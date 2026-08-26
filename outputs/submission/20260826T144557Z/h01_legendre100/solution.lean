import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  have h₁ : 3 ^ 48 ∣ Nat.factorial 100 := by
    -- Using Legendre's formula: v₃(100!) = ⌊100/3⌋ + ⌊100/9⌋ + ⌊100/27⌋ + ⌊100/81⌋ = 33 + 11 + 3 + 1 = 48
    norm_num [Nat.dvd_factorial]
    <;> decide
  
  have h₂ : ∀ k : ℕ, 3 ^ k ∣ Nat.factorial 100 → k ≤ 48 := by
    intro k hk
    -- If k > 48, then v₃(k!) would be at least k > 48, but we know it's exactly 48
    have h : k ≤ 48 := by
      by_contra h'
      -- If k > 48, then 3^(48+1) divides 100!
      have h'' : 3 ^ (48 + 1) ∣ Nat.factorial 100 := by
        have h''' : 3 ^ k ∣ Nat.factorial 100 := hk
        have h'''' : 48 + 1 ≤ k := by omega
        exact dvd_trans (pow_dvd_pow _ h'''' ) h'''
      -- But v₃(100!) = 48, so 3^49 does not divide 100!
      norm_num at h''
      <;> simp_all [Nat.dvd_factorial]
      <;> norm_num
      <;> omega
    exact h
  
  exact ⟨h₁, h₂⟩
