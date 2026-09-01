import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  have h_gcd : Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) = 1 := by
    set d := Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) with hd
    have h1 : d ∣ Nat.factorial n + 1 := Nat.gcd_dvd_left _ _
    have h2 : d ∣ Nat.factorial (n + 1) + 1 := Nat.gcd_dvd_right _ _
    
    -- d divides (n+1)(n! + 1)
    have h3 : d ∣ (n + 1) * (Nat.factorial n + 1) := dvd_mul_of_dvd_right h1 (n + 1)
    
    -- Expand (n+1)(n! + 1) = (n+1)! + n + 1
    have h4 : (n + 1) * (Nat.factorial n + 1) = Nat.factorial (n + 1) + n + 1 := by
      simp [Nat.factorial_succ, mul_add, add_assoc]
      <;> ring
    
    rw [h4] at h3
    
    -- Show d divides n
    -- We have d | (n+1)! + n + 1 and d | (n+1)! + 1
    -- Need (n+1)! + 1 ≤ (n+1)! + n + 1
    have h5 : Nat.factorial (n + 1) + 1 ≤ Nat.factorial (n + 1) + n + 1 := by
      omega
    
    have h6 : d ∣ n := by
      apply Nat.dvd_sub' h3 h2
      exact h5
      
    -- Show d divides n!
    have h7 : d ∣ Nat.factorial n := by
      have h8 : d ∣ n := h6
      have h9 : n ∣ Nat.factorial n := Nat.dvd_factorial hn
      exact dvd_trans h8 h9
      
    -- Show d divides 1
    have h10 : d ∣ 1 := by
      have h11 : d ∣ Nat.factorial n + 1 := h1
      have h12 : d ∣ Nat.factorial n := h7
      have h13 : Nat.factorial n ≤ Nat.factorial n + 1 := by
        apply Nat.le_add_right
      have h14 : d ∣ (Nat.factorial n + 1) - Nat.factorial n := by
        apply Nat.dvd_sub' h11 h12
        exact h13
      simpa [Nat.add_sub_cancel] using h14
      
    -- Conclude d = 1
    have h15 : d = 1 := Nat.dvd_one.mp h10
    rw [hd] at h15
    exact h15
  
  rw [Nat.coprime_iff_gcd_eq_one]
  exact h_gcd
