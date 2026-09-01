import Mathlib.NumberTheory.LegendreFormula
import Mathlib.Tactic

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Show that 48 ∈ {k | 3^k ∣ 100!}
    rw [h01_answer]
    apply Nat.pow_dvd_factorial_of_le
    norm_num
  · -- Show that for any k > 48, 3^k does not divide 100!
    intro k hk
    simp only [Set.mem_setOf_eq, h01_answer] at hk ⊢
    have h : padicValNat 3 (Nat.factorial 100) = 48 := by
      rw [padicValNat.factorial]
      norm_num [Nat.factorial]
    have h' : ¬(3 ^ k ∣ Nat.factorial 100) := by
      intro hdiv
      have hval : padicValNat 3 (Nat.factorial 100) ≥ k := by
        apply padicValNat.le_of_dvd
        · exact Nat.factorial_pos 100
        · exact hdiv
      linarith
    contradiction
