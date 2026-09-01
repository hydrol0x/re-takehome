import Mathlib

open Nat

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  -- First step of the Euclidean algorithm:
  have h₁ :
      Nat.gcd (2 * n + 1) (9 * n + 4) =
        Nat.gcd (2 * n + 1) ((9 * n + 4) % (2 * n + 1)) := by
    simpa [Nat.gcd_comm] using Nat.gcd_mod_left (2 * n + 1) (9 * n + 4)

  -- Compute the remainder ` (9 * n + 4) % (2 * n + 1) = n `
  have hrem : (9 * n + 4) % (2 * n + 1) = n := by
    have : 9 * n + 4 = (2 * n + 1) * 4 + n := by ring
    -- rewrite the left‑hand side using this equality and `Nat.mod_mul_left_mod`
    simpa [this, Nat.mod_mul_left_mod, Nat.mod_eq_of_lt (by
      have : n < 2 * n + 1 := by
        cases n with
        | zero => simp
        | succ n' =>
          have : (Nat.succ n') ≤ 2 * Nat.succ n' := by
            have : (Nat.succ n') ≤ Nat.succ n' + Nat.succ n' := Nat.le_add_self
            simpa [Nat.succ_mul, Nat.mul_comm, Nat.mul_add, Nat.add_comm,
                  Nat.add_left_comm, Nat.add_assoc] using this
          exact Nat.lt_of_le_of_lt this (Nat.lt_succ_self _)
      exact this)]

  -- Replace the remainder in `h₁`
  have h₂ : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by
    simpa [hrem] using h₁

  -- Second step of the Euclidean algorithm:
  have h₃ :
      Nat.gcd (2 * n + 1) n = Nat.gcd ((2 * n + 1) % n) n := by
    simpa [Nat.gcd_comm] using Nat.gcd_mod_right (2 * n + 1) n

  -- Compute the remainder ` (2 * n + 1) % n = 1 `
  have hmod : (2 * n + 1) % n = 1 := by
    cases n with
    | zero => simp
    | succ n' =>
        have : (2 * Nat.succ n' + 1) % Nat.succ n' = 1 := by
          -- write the number as `n * 2 + 1`
          have : (2 * Nat.succ n' + 1) = Nat.succ n' * 2 + 1 := by ring
          -- use `Nat.mod_mul_left_mod` and `Nat.mod_eq_of_lt`
          simpa [this, Nat.mod_mul_left_mod,
                 Nat.mod_eq_of_lt (Nat.succ_pos _)] 
        simpa using this

  -- Hence the gcd is `1`
  have h₄ : Nat.gcd (2 * n + 1) n = 1 := by
    simpa [hmod] using h₃

  simpa [h₂] using h₄
