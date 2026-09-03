import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set d := Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) with hd
  have h1 : d ∣ Nat.factorial n + 1 := Nat.gcd_dvd_left _ _
  have h2 : d ∣ Nat.factorial (n + 1) + 1 := Nat.gcd_dvd_right _ _
  have h3 : d ∣ (n + 1) * (Nat.factorial n + 1) := Dvd.dvd.mul_left h1 (n + 1)
  have h4 : (n + 1) * (Nat.factorial n + 1) = Nat.factorial (n + 1) + (n + 1) := by
    rw [Nat.factorial_succ]; ring
  rw [h4] at h3
  have h5 : d ∣ n := by
    have hgen : ∀ F : ℕ, F + (n + 1) - (F + 1) = n := fun F => by omega
    have h6 := Nat.dvd_sub h3 h2
    rwa [hgen (Nat.factorial (n + 1))] at h6
  have h7 : d ∣ Nat.factorial n := h5.trans (Nat.dvd_factorial hn le_rfl)
  have h8 : d ∣ 1 := by
    have h9 := Nat.dvd_sub h1 h7
    rwa [Nat.add_sub_cancel_left] at h9
  exact Nat.dvd_one.mp h8
