import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  -- Prove that the gcd is `1`.
  have h_gcd_one :
      Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) = 1 := by
    set d := Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) with hddef
    have hd_left : d ∣ Nat.factorial n + 1 := by
      have := Nat.gcd_dvd_left (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1)
      simpa [hddef] using this
    have hd_right : d ∣ Nat.factorial (n + 1) + 1 := by
      have := Nat.gcd_dvd_right (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1)
      simpa [hddef] using this
    have hd_mul : d ∣ (n + 1) * (Nat.factorial n + 1) :=
      Nat.dvd_mul_of_dvd_left hd_left (n + 1)
    have hd_sub :
        d ∣ (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) :=
      Nat.dvd_sub hd_mul hd_right
    have hd_n : d ∣ n := by
      have hcalc :
          (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) = n := by
        simp [Nat.factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      simpa [hcalc] using hd_sub
    have hd_fact : d ∣ Nat.factorial n := by
      have hnf : n ∣ Nat.factorial n := Nat.dvd_factorial (Nat.le_refl n)
      exact Nat.dvd_trans hd_n hnf
    have hd_one : d ∣ 1 := by
      have := Nat.dvd_sub hd_left hd_fact
      simpa [Nat.add_sub_cancel] using this
    have : d = 1 := (Nat.dvd_one.mp hd_one)
    simpa [hddef] using this
  exact Nat.coprime_of_gcd_eq_one h_gcd_one
