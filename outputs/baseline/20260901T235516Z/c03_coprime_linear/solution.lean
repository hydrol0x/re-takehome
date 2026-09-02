import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  -- First show `n` is coprime with `1`
  have h0 : n.Coprime 1 := Nat.coprime_one_left _
  -- Hence `n` is coprime with `1 + n * 2 = 2 * n + 1`
  have h1 : n.Coprime (1 + n * 2) := Nat.coprime_add_mul_left_right h0 2
  have h2 : (2 * n + 1).Coprime n := by
    have h1' : n.Coprime (2 * n + 1) := by
      simpa [two_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
        add_assoc] using h1
    exact (Nat.coprime_comm).1 h1'
  -- From this we get coprimality with `9 * n + 4 = n + (2 * n + 1) * 4`
  have h3 : (2 * n + 1).Coprime (9 * n + 4) := by
    have := Nat.coprime_add_mul_left_right h2 4
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
      add_assoc, left_distrib, right_distrib] using this
  -- Translate coprimality to a statement about the gcd
  have : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 :=
    (Nat.coprime_iff_gcd_eq_one).mp h3
  simpa using this
