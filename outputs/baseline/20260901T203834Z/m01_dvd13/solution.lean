import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- rewrite the goal in a convenient form
      have h_eq :
          4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2) =
            16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by
        have h1 : 2 * (n + 1) + 1 = 2 * n + 3 := by
          simp [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        have h2 : (n + 1) + 2 = n + 3 := by
          simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        simp [h1, h2, pow_add, pow_two, mul_comm, mul_left_comm, mul_assoc]
      -- induction hypothesis as a modular equality
      have hmod :
          (4 ^ (2 * n + 1) + 3 ^ (n + 2)) ≡ 0 [MOD 13] :=
        (Nat.ModEq.zero_iff_dvd).2 ih
      -- 16 ≡ 3 (mod 13)
      have hcoeff : (16 : ℕ) ≡ 3 [MOD 13] := by norm_num
      -- replace 16 by 3 in the expression
      have h1 :
          (16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) ≡
            (3 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) [MOD 13] := by
        have hmul : (16 * 4 ^ (2 * n + 1)) ≡ (3 * 4 ^ (2 * n + 1)) [MOD 13] :=
          hcoeff.mul_left _
        exact hmul.add_right (3 * 3 ^ (n + 2))
      -- use the induction hypothesis multiplied by 3
      have h2 :
          (3 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) ≡ 0 [MOD 13] := by
        simpa [mul_add] using hmod.mul_left 3
      have hfinal :
          (16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) ≡ 0 [MOD 13] :=
        h1.trans h2
      have : 13 ∣ 16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) :=
        (Nat.ModEq.zero_iff_dvd).1 hfinal
      simpa [h_eq] using this
