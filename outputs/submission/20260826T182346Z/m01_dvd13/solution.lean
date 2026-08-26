import Mathlib.Tactic

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
    -- Base case: n = 0
    -- 4^(2*0+1) + 3^(0+2) = 4^1 + 3^2 = 4 + 9 = 13
    norm_num
  | succ n ih =>
    -- Inductive step: assume true for n, prove for n+1
    -- 4^(2*(n+1)+1) + 3^((n+1)+2) = 4^(2*n+3) + 3^(n+3)
    -- = 16 * 4^(2*n+1) + 3 * 3^(n+2)
    -- = 13 * 4^(2*n+1) + 3 * (4^(2*n+1) + 3^(n+2))
    have h1 : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := ih
    have h2 : 13 ∣ 13 * 4 ^ (2 * n + 1) := dvd_mul_right 13 _
    have h3 : 13 ∣ 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) := dvd_mul_of_dvd_right h1 3
    have h4 : 13 ∣ 13 * 4 ^ (2 * n + 1) + 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) :=
      dvd_add h2 h3
    -- Simplify the expression
    simp [pow_add, pow_one, pow_two, Nat.mul_succ] at h4 ⊢
    <;> ring_nf at h4 ⊢ <;> omega
