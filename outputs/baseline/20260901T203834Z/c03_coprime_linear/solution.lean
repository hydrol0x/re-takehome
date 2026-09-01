import Mathlib
import Mathlib.Tactic

open Nat

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  -- we prove the stronger statement that the two numbers are coprime
  have h_coprime : Nat.Coprime (2 * n + 1) (9 * n + 4) := by
    -- first show that `2 * n + 1` is coprime with `n`
    have h₁ : Nat.Coprime (2 * n + 1) n := by
      -- any common divisor of `2 * n + 1` and `n` also divides their difference `1`
      have h : Nat.Coprime 1 n := Nat.coprime_one_left _
      -- use the lemma `coprime_add_left_iff` which says `Coprime (a + b) b ↔ Coprime a b`
      simpa [two_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using (Nat.coprime_add_left
