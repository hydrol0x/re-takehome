import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    have h1 : 4 ^ (2 * (n + 1) + 1) = 16 * 4 ^ (2 * n + 1) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add]; ring
    have h2 : 3 ^ (n + 1 + 2) = 3 * 3 ^ (n + 2) := by
      rw [show n + 1 + 2 = (n + 2) + 1 by ring, pow_add]; ring
    refine ⟨3 * k + 4 ^ (2 * n + 1), ?_⟩
    rw [h1, h2]
    linarith [hk]
