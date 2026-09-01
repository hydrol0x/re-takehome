import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  -- we use the characterisation via the gcd
  apply (Nat.coprime_iff_gcd_eq_one).2
  -- let `d` be the gcd of the two numbers
  set d := Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) with hd
  -- we show that `d ∣ 1`, which forces `d = 1`
  have hd1 : d ∣ 1 := by
    -- `d` divides each of the two numbers
    have hda : d ∣ Nat.factorial n + 1 := by
      have := Nat.gcd_dvd_left (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1)
      simpa [hd] using this
    have hdb : d ∣ Nat.factorial (n + 1) + 1 := by
      have := Nat.gcd_dvd_right (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1)
      simpa [hd] using this
    -- from the two divisibilities we get `d ∣ n`
    have hdmul : d ∣ (n + 1) * (Nat.factorial n + 1) :=
      Nat.dvd_mul_of_dvd_left hda _
    have hle : Nat.factorial (n + 1) + 1 ≤ (n + 1) * (Nat.factorial n + 1) := by
      have h_eq :
          (n + 1) * (Nat.factorial n + 1) = Nat.factorial (n + 1) + (n + 1) := by
        calc
          (n + 1) * (Nat.factorial n + 1)
              = (n + 1) * Nat.factorial n + (n + 1) * 1 := by
                simpa [Nat.mul_add, Nat.mul_one] using (Nat.mul_add (n + 1) (Nat.factorial n) 1)
          _ = Nat.factorial (n + 1) + (n + 1) := by
                simpa [Nat.factorial_succ, Nat.mul_one, Nat.add_comm, Nat.add_left_comm,
                      Nat.add_assoc]
      have h_one_le : (1 : ℕ) ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      have : Nat.factorial (n + 1) + 1 ≤ Nat.factorial (n + 1) + (n + 1) :=
        Nat.add_le_add_left h_one_le _
      simpa [h_eq] using this
    have hsub : d ∣ (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) :=
      Nat.dvd_sub hdmul hdb hle
    have hsub_eq : (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) = n := by
      calc
        (n + 1) * (Nat.factorial n +
