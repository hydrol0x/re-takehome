import Mathlib

/-- A positive integer `n` satisfies `(n + 2) ∣ n ^ 2 + 4` iff `n = 2` or `n = 6`. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · intro h
    have h1 : (n + 2) ∣ n ^ 2 + 4 * n + 4 := ⟨n + 2, by ring⟩
    have h2 : (n + 2) ∣ 4 * n := by
      have hs : ∀ s : ℕ, s + 4 * n + 4 - (s + 4) = 4 * n := fun s => by omega
      have h6 := Nat.dvd_sub h1 h
      rwa [show n ^ 2 + 4 * n + 4 - (n ^ 2 + 4) = 4 * n from hs (n ^ 2)] at h6
    have h3 : (n + 2) ∣ 4 * n + 8 := ⟨4, by ring⟩
    have h4 : (n + 2) ∣ 8 := by
      have h7 := Nat.dvd_sub h3 h2
      rwa [show 4 * n + 8 - 4 * n = 8 by omega] at h7
    have h5 : n + 2 ≤ 8 := Nat.le_of_dvd (by norm_num) h4
    have h6 : n ≤ 6 := by omega
    interval_cases n <;> revert h <;> decide
  · rintro (rfl | rfl) <;> decide
