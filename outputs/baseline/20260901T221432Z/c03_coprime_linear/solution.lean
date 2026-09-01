import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  -- first show that `2 * n + 1` is coprime with `n`
  have h1 : Nat.Coprime (2 * n + 1) n := by
    have : (2 * n + 1) - 2 * n = 1 := by
      ring
    exact Nat.coprime_of_sub_eq_one this
  -- coprime is preserved when adding a multiple of the first number to the second
  have h2 : Nat.Coprime (2 * n + 1) (n + 4 * (2 * n + 1)) :=
    Nat.coprime_add_mul_left_right h1 4
  -- rewrite the second argument to the required form
  simpa [mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
    mul_assoc] using h2
