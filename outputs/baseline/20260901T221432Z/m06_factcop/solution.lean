import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  -- Let `d` be the gcd of the two numbers.
  set d := Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) with hddef
  have hd_left : d ∣ Nat.factorial n + 1 := by
    have := Nat.gcd_dvd_left (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1)
    simpa [hddef] using this
  have hd_right : d ∣ Nat.factorial (n + 1) + 1 := by
    have := Nat.gcd_dvd_right (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1)
    simpa [hddef] using this
  -- From the two divisibilities we get `d ∣ n`.
  have hd_mul : d ∣ (n + 1) * (Nat.factorial n + 1) :=
    Nat.dvd_mul_of_dvd_left hd_left (n + 1)
  have hle : Nat.factorial (n + 1) + 1 ≤ (n + 1) * (Nat.factorial n + 1) := by
    have h_one_le : (1 : ℕ) ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    calc
      Nat.factorial (n + 1) + 1
          ≤ Nat.factorial (n + 1) + (n + 1) := by
            exact Nat.add_le_add_left h_one_le _
      _ = (n + 1) * (Nat.factorial n + 1) := by
            simp [Nat.factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
                  Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hd_sub : d ∣ (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) :=
    Nat.dvd_sub hle hd_mul hd_right
  have hd_n : d ∣ n := by
    simpa [Nat.factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hd_sub
  -- `n` is positive, hence `d ≤ n`.
  have hpos_n : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_one) hn
  have hd_le_n : d ≤ n := Nat.le_of_dvd hpos_n hd_n
  -- Therefore `d ∣ n!`.
  have hd_fact : d ∣ Nat.factorial n := Nat.dvd_factorial hd_le_n
  -- Now `d` divides `(n! + 1) - n! = 1`.
  have hd_one : d ∣ 1 := by
    have hle' : Nat.factorial n ≤ Nat.factorial n + 1 := Nat.le_succ _
    have := Nat.dvd_sub hle' hd_left hd_fact
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  -- Hence `d = 1`.
  have hgd : d = 1 := Nat.dvd_one.mp hd_one
  -- Conclude coprimality.
  have : Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) = 1 := by
    simpa [hddef] using hgd
  exact (Nat.coprime_iff_gcd_eq_one).mpr this
