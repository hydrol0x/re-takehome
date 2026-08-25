import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h1 : Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) ((9 * n + 4) % (2 * n + 1)) := by
    rw [← Nat.mod_add_div (9 * n + 4) (2 * n + 1)]
    simp [Nat.gcd_comm]
    <;> ring_nf
    <;> simp [Nat.gcd_comm]
  
  have h2 : (9 * n + 4) % (2 * n + 1) = n := by
    have h3 : 9 * n + 4 = 4 * (2 * n + 1) + n := by
      ring
    rw [h3]
    have h4 : n < 2 * n + 1 := by
      omega
    simp [Nat.add_mod, Nat.mul_mod, h4]
  
  rw [h1, h2]
  
  have h5 : Nat.gcd (2 * n + 1) n = Nat.gcd 1 n := by
    have h6 : 2 * n + 1 = 2 * n + 1 := rfl
    have h7 : Nat.gcd (2 * n + 1) n = Nat.gcd (2 * n + 1 - 2 * n) n := by
      rw [← Nat.gcd_comm]
      simpa [Nat.gcd_comm] using Nat.gcd_eq_right (show n ∣ 2 * n + 1 - (2 * n + 1 - n) by
        omega)
    rw [h7]
    <;> norm_num
    <;> ring_nf
  
  rw [h5]
  simp [Nat.gcd_one_left]
