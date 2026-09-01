import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  have h_factorial_succ : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
    simp [Nat.factorial_succ]
  
  let g := Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1)
  
  have hg_dvd_a : g ∣ Nat.factorial n + 1 := Nat.gcd_dvd_left _ _
  have hg_dvd_b : g ∣ Nat.factorial (n + 1) + 1 := Nat.gcd_dvd_right _ _
  
  have hg_dvd_mul : g ∣ (n + 1) * (Nat.factorial n + 1) := dvd_mul_of_dvd_right hg_dvd_a _
  
  have h_mul_eq : (n + 1) * (Nat.factorial n + 1) = Nat.factorial (n + 1) + (n + 1) := by
    rw [h_factorial_succ]
    ring
  
  have hg_dvd_sum : g ∣ Nat.factorial (n + 1) + (n + 1) := by
    rw [← h_mul_eq]
    exact hg_dvd_mul
  
  have hg_dvd_n : g ∣ n := by
    have h_diff : Nat.factorial (n + 1) + (n + 1) - (Nat.factorial (n + 1) + 1) = n := by
      omega
    have hg_dvd_diff : g ∣ Nat.factorial (n + 1) + (n + 1) - (Nat.factorial (n + 1) + 1) := by
      apply Nat.dvd_sub'
      · exact hg_dvd_sum
      · exact hg_dvd_b
    rw [h_diff] at hg_dvd_diff
    exact hg_dvd_diff
  
  have hg_dvd_fact : g ∣ Nat.factorial n := by
    have h_g_dvd_n : g ∣ n := hg_dvd_n
    have h_n_dvd_fact : n ∣ Nat.factorial n := Nat.dvd_factorial hn
    exact dvd_trans h_g_dvd_n h_n_dvd_fact
  
  have hg_dvd_one : g ∣ 1 := by
    have h_diff : (Nat.factorial n + 1) - Nat.factorial n = 1 := by
      omega
    have hg_dvd_diff : g ∣ (Nat.factorial n + 1) - Nat.factorial n := by
      apply Nat.dvd_sub'
      · exact hg_dvd_a
      · exact hg_dvd_fact
    rw [h_diff] at hg_dvd_diff
    exact hg_dvd_diff
  
  have hg_eq_one : g = 1 := Nat.eq_one_of_dvd_one hg_dvd_one
  
  rw [hg_eq_one]
  simp [Nat.Coprime]
