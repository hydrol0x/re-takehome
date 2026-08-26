import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show 4 ^ (2 * (n + 1) + 1) = 16 * 4 ^ (2 * n + 1) by ring]
    rw [show 3 ^ ((n + 1) + 2) = 3 * 3 ^ (n + 2) by ring]
    have : 16 ≡ 3 [MOD 13] := by norm_num
    omega
