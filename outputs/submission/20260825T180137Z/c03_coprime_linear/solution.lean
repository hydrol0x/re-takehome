import Mathlib.Tactic

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h1 : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) ((9 * n + 4) % (2 * n + 1)) := by
    rw [← Nat.mod_add_div (9 * n + 4) (2 * n + 1)]
    simp [Nat.gcd_comm]
    <;> ring_nf
    <;> rw [Nat.gcd_comm]
  
  have h2 : (9 * n + 4) % (2 * n + 1) = n := by
    have h3 : 9 * n + 4 = 4 * (2 * n + 1) + n := by
      ring
    rw [h3]
    have h4 : n < 2 * n + 1 := by
      omega
    rw [Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt h4]
    
  rw [h1, h2]
  
  have h5 : Nat.gcd (2 * n + 1) n = Nat.gcd 1 n := by
    have h6 : 2 * n + 1 = 2 * n + 1 := rfl
    rw [show 2 * n + 1 = 2 * n + 1 by rfl]
    have h7 : Nat.gcd (2 * n + 1) n = Nat.gcd 1 n := by
      have h8 : 2 * n + 1 = 2 * n + 1 := rfl
      rw [← Nat.mod_add_div (2 * n + 1) n]
      simp [Nat.add_mod, Nat.mul_mod]
      <;> cases n with
      | zero => simp
      | succ n' =>
        simp [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_mul, Nat.add_assoc]
        <;> ring_nf at *
        <;> simp_all [Nat.gcd_comm]
        <;> omega
    exact h7
  
  rw [h5]
  simp [Nat.gcd_one_left]
