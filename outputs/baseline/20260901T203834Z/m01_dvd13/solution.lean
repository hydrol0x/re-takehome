import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
      -- base case: 4¹ + 3² = 13
      simp
  | succ n ih =>
      -- induction hypothesis as a congruence
      have hmod :
          (4 ^ (2 * n + 1) + 3 ^ (n + 2)) ≡ 0 [MOD 13] :=
        (Nat.ModEq.zero_iff_dvd).2 ih
      -- 16 ≡ 3 (mod 13)
      have h16 : (16 : ℕ) ≡ 3 [MOD 13] := by
        norm_num
      -- rewrite the expression for `n+1`
      have hE :
          4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2) =
            16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by
        have h1 : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
        have h2 : (n + 1) + 2 = n + 3 := by ring
        simp [h1, h2, Nat.pow_add, Nat.pow_succ, pow_two,
              mul_comm, mul_left_comm, mul_assoc]
      -- prove the rewritten expression is 0 mod 13
      have hfinal :
          (16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) ≡ 0 [MOD 13] := by
        calc
          16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)
              ≡ 3 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by
                simpa [h16]
          _ ≡ 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) := by
                simpa [mul_add, add_comm, add_left_comm, add_assoc]
          _ ≡ 0 := by
                simpa using (hmod.mul_left 3)
      -- combine the rewrite with the congruence
      have : (4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2)) ≡ 0 [MOD 13] := by
        simpa [hE] using hfinal
      exact (Nat.ModEq.zero_iff_dvd).1 this
