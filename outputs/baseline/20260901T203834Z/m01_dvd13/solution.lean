import Mathlib

open Nat

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- first prove the statement for the rewritten form
      have hstep : 13 ∣ 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by
        have h13 : 13 ∣ 13 * 4 ^ (2 * n + 1) :=
          Nat.dvd_mul_of_dvd_left (Nat.dvd_refl 13) _
        have h3 : 13 ∣ 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) :=
          Nat.dvd_mul_of_dvd_left ih 3
        have hsum :
            13 ∣ 13 * 4 ^ (2 * n + 1) + 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) :=
          Nat.dvd_add h13 h3
        have : 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) =
                13 * 4 ^ (2 * n + 1) + 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) := by
          ring
        simpa [this] using hsum
      -- rewrite the goal to the above form
      simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
            Nat.pow_add, pow_two, Nat.pow_succ,
            mul_comm, mul_left_comm, mul_assoc] using hstep
