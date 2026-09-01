import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-- A positive integer `n` satisfies `(n + 2) ∣ n ^ 2 + 4` iff `n = 2` or `n = 6`. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · intro hdiv
    -- from the hypothesis we also have `(n+2) ∣ (n+2)^2`
    have hsq : (n + 2) ∣ (n + 2) ^ 2 := by
      exact dvd_mul_left _ _
    -- subtract to obtain `(n+2) ∣ 4 * n`
    have h4n : (n + 2) ∣ 4 * n := by
      have := dvd_sub hsq hdiv
      simpa [pow_two, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc, sub_eq, sub_eq_iff_eq_add] using this
    -- also `(n+2) ∣ 4 * (n+2)`
    have h4np2 : (n + 2) ∣ 4 * (n + 2) := by
      exact dvd_mul_left _ _
    -- subtract again to get `(n+2) ∣ 8`
    have h8 : (n + 2) ∣ 8 := by
      have := dvd_sub h4np2 h4n
      simpa [Nat.mul_sub_left_distrib, add_comm, add_left_comm, add_assoc,
        Nat.add_sub_cancel] using this
    -- hence `n+2 ≤ 8`, so `n ≤ 6`
    have hle : n + 2 ≤ 8 := Nat.le_of_dvd (Nat.succ_pos _) h8
    have hle' : n ≤ 6 := by
      linarith
    -- now check the finitely many possibilities
    have hcases :
        n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
      interval_cases n using hle'
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · -- n = 1, contradiction
      have : ¬ (3 ∣ 5) := by decide
      exact (this hdiv).elim
    · -- n = 2
      exact Or.inl rfl
    · -- n = 3, contradiction
      have : ¬ (5 ∣ 13) := by decide
      exact (this hdiv).elim
    · -- n = 4, contradiction
      have : ¬ (6 ∣ 20) := by decide
      exact (this hdiv).elim
    · -- n = 5, contradiction
      have : ¬ (7 ∣ 29) := by decide
      exact (this hdiv).elim
    · -- n = 6
      exact Or.inr rfl
  · intro h
    rcases h with rfl | rfl
    · -- n = 2
      simp
    · -- n = 6
      simp
