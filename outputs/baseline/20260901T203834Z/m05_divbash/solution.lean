import Mathlib
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-- A positive integer `n` satisfies `(n + 2) ∣ n ^ 2 + 4` iff `n = 2` or `n = 6`. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · intro h
    -- From the hypothesis we get `(n+2) ∣ 8`
    have h1 : (n + 2) ∣ (n + 2) ^ 2 := by
      simpa [pow_two] using dvd_mul_left (n + 2) (n + 2)
    have hdiff : (n + 2) ∣ (n + 2) ^ 2 - (n ^ 2 + 4) := Nat.dvd_sub h1 h
    have h4n : (n + 2) ∣ 4 * n := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc,
        Nat.add_sub_cancel] using hdiff
    have h4np2 : (n + 2) ∣ 4 * (n + 2) := by
      simpa using dvd_mul_left (n + 2) 4
    have h8 : (n + 2) ∣ 8 := by
      have := Nat.dvd_sub h4np2 h4n
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hpos : 0 < n + 2 := Nat.succ_pos _
    have hle : n + 2 ≤ 8 := Nat.le_of_dvd hpos h8
    have hle' : n ≤ 6 := by
      linarith
    have hge' : 1 ≤ n := Nat.succ_le_of_lt hn
    have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
      interval_cases n using Nat with hge' hle'
    rcases hcases with h1 | h2 | h3 | h4 | h5 | h6
    · have : (1 + 2) ∣ 1 ^ 2 + 4 := by simpa [h1] using h
      simp at this
    · exact Or.inl (by simpa [h2])
    · have : (3 + 2) ∣ 3 ^ 2 + 4 := by simpa [h3] using h
      simp at this
    · have : (4 + 2) ∣ 4 ^ 2 + 4 := by simpa [h4] using h
      simp at this
    · have : (5 + 2) ∣ 5 ^ 2 + 4 := by simpa [h5] using h
      simp at this
    · exact Or.inr (by simpa [h6])
  · intro h
    rcases h with rfl | rfl
    · have : (2 + 2) ∣ 2 ^ 2 + 4 := by norm_num
      simpa using this
    · have : (6 + 2) ∣ 6 ^ 2 + 4 := by norm_num
      simpa using this
