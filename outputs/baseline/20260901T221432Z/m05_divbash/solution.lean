import Mathlib
open Nat

/-- A positive integer `n` satisfies `(n + 2) ∣ n ^ 2 + 4` iff `n = 2` or `n = 6`. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · intro h
    -- also divides its square
    have hsq : (n + 2) ∣ (n + 2) ^ 2 := dvd_mul_left _ _
    -- subtract the two multiples
    have h4n : (n + 2) ∣ 4 * n := by
      have := dvd_sub hsq h
      simpa [pow_two, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using this
    -- divide 4·(n+2)
    have h4s : (n + 2) ∣ 4 * (n + 2) := dvd_mul_left _ _
    have h8 : (n + 2) ∣ 8 := by
      have := dvd_sub h4s h4n
      simpa [Nat.mul_add, Nat.add_mul, mul_comm, mul_left_comm, mul_assoc] using this
    -- bound n
    have hle : n + 2 ≤ 8 := Nat.le_of_dvd (Nat.succ_pos _) h8
    have hle' : n ≤ 6 := by
      have := Nat.le_of_add_le_add_left (by
        simpa [add_comm, add_left_comm, add_assoc] using hle)
      simpa using this
    -- finite check
    have : n = 2 ∨ n = 6 := by
      interval_cases n using hle'
      · -- n = 0, contradict positivity
        exfalso
        exact lt_irrefl _ (by simpa [*] using hn)
      · -- n = 1, impossible
        exfalso
        have h' : (1 + 2) ∣ 1 ^ 2 + 4 := by simpa using h
        have : ¬ (3 : ℕ) ∣ 5 := by decide
        exact this h'
      · -- n = 2
        exact Or.inl rfl
      · -- n = 3, impossible
        exfalso
        have h' : (3 + 2) ∣ 3 ^ 2 + 4 := by simpa using h
        have : ¬ (5 : ℕ) ∣ 13 := by decide
        exact this h'
      · -- n = 4, impossible
        exfalso
        have h' : (4 + 2) ∣ 4 ^ 2 + 4 := by simpa using h
        have : ¬ (6 : ℕ) ∣ 20 := by decide
        exact this h'
      · -- n = 5, impossible
        exfalso
        have h' : (5 + 2) ∣ 5 ^ 2 + 4 := by simpa using h
        have : ¬ (7 : ℕ) ∣ 29 := by decide
        exact this h'
      · -- n = 6
        exact Or.inr rfl
    exact this
  · intro h
    rcases h with rfl | rfl
    · norm_num
    · norm_num
