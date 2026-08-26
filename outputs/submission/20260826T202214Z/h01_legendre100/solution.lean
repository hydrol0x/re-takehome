import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Prove 3^48 divides 100!
    norm_num [Nat.factorial]
    <;> decide
  · -- Prove for all k where 3^k divides 100!, we have k ≤ 48
    intro k hk
    rw [Set.mem_setOf] at hk
    -- Use Legendre's formula: v_3(100!) = ⌊100/3⌋ + ⌊100/9⌋ + ⌊100/27⌋ + ⌊100/81⌋ = 33 + 11 + 3 + 1 = 48
    have h : k ≤ 48 := by
      by_contra h
      have h' : k ≥ 49 := by omega
      -- If k ≥ 49, then 3^49 must divide 100!, but it doesn't
      have h_div : 3 ^ 49 ∣ Nat.factorial 100 := by
        calc
          3 ^ 49 ∣ 3 ^ k := Nat.pow_dvd_pow _ (by omega)
          _ ∣ Nat.factorial 100 := hk
      norm_num [Nat.factorial] at h_div
      <;> contradiction
    exact h
