import Mathlib
import Mathlib.Tactic

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
      -- 4¹ + 3² = 13
      simp
  | succ n ih =>
      -- induction hypothesis as a ModEq
      have hmod_sum : (4 ^ (2 * n + 1) + 3 ^ (n + 2)) ≡ 0 [MOD 13] :=
        (Nat.ModEq.zero_iff_dvd).mpr ih
      -- 16 ≡ 3 (mod 13)
      have h16 : (16 : ℕ) ≡ 3 [MOD 13] := by norm_num
      -- rewrite the goal expression
      have hexpr :
          4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2) =
            16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by
        have h1 : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
        have h2 : (n + 1) + 2 = n + 3 := by ring
        simp [h1, h2, pow_add, pow_two, mul_comm, mul_left_comm, mul_assoc] 
      -- work modulo 13
      have : (16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) ≡ 0 [MOD 13] := by
        -- replace 16 by 3
        have h16_mul : (16 * 4 ^ (2 * n + 1)) ≡ (3 * 4 ^ (2 * n + 1)) [MOD 13] :=
          h16.mul_left _
        have hsum :
            (16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) ≡
              (3 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) [MOD 13] :=
          h16_mul.add (Nat.ModEq.refl _)
        have hfactor :
            (3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2))) ≡
              (3 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) [MOD 13] := by
          simpa [mul_add, add_comm, add_left_comm, add_assoc,
                 mul_comm, mul_left_comm, mul_assoc] using
            (Nat.ModEq.refl (4 ^ (2 * n + 1) + 3 ^ (n + 2))).mul_left 3
        have hzero : (3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2))) ≡ 0 [MOD 13] :=
          hmod_sum.mul_left 3
        calc
          (16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2))
              ≡ (3 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) := hsum
          _ ≡ 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) := by
                simpa [mul_add, add_comm, add_left_comm, add_assoc,
                       mul_comm, mul_left_comm, mul_assoc] using hfactor.symm
          _ ≡ 0 := hzero
      -- conclude using the rewritten expression
      have hmod : (4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2)) ≡ 0 [MOD 13] := by
        simpa [hexpr] using this
      exact (Nat.ModEq.zero_iff_dvd).mp hmod
