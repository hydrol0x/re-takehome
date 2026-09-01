import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  -- `n!` and `n! + 1` are coprime
  have h_coprime_fact : Nat.Coprime (Nat.factorial n) (Nat.factorial n + 1) :=
    Nat.coprime_self_add_one (Nat.factorial n)
  have h_coprime_fact' : Nat.Coprime (Nat.factorial n + 1) (Nat.factorial n) :=
    h_coprime_fact.symm
  -- `n!` divides `n * n!`
  have h_dvd : Nat.factorial n ∣ n * Nat.factorial n := Nat.dvd_mul_right _ _
  -- therefore `n! + 1` is coprime with `n * n!`
  have h_coprime_mul : Nat.Coprime (Nat.factorial n + 1) (n * Nat.factorial n) :=
    Nat.coprime_of_dvd_mul_right h_coprime_fact' h_dvd
  -- rewrite `(n+1)! + 1` as `(n! + 1) + n * n!`
  have h_eq :
      Nat.factorial (n + 1) + 1 = (Nat.factorial n + 1) + n * Nat.factorial n := by
    simp [Nat.factorial_succ, mul_add, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc]
  -- use `coprime_add_self_right` to add the common term `n! + 1`
  have h_final :
      Nat.Coprime (Nat.factorial n + 1) ((Nat.factorial n + 1) + n * Nat.factorial n) := by
    exact (Nat.coprime_add_self_right (Nat.factorial n + 1) (n * Nat.factorial n)).mpr
      h_coprime_mul
  simpa [h_eq] using h_final
