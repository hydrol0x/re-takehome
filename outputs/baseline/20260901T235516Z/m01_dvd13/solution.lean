import Mathlib

open Nat

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
      refine ⟨1, ?_⟩
      simp
  | succ n ih =>
      -- induction hypothesis as a congruence modulo 13
      have ih_mod :
          (4 ^ (2 * n + 1) + 3 ^ (n + 2)) ≡ (0 : ℕ) [MOD 13] :=
        (Nat.ModEq.zero_iff_dvd).2 ih
      -- 16 ≡ 3 (mod 13)
      have h16 : (16 : ℕ) ≡ 3 [MOD 13] := by norm_num
      -- rewrite the expression for the successor case
      have hrew :
          4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2) =
            16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2) := by
        simp [Nat.mul_succ, add_comm, add_left_comm, add_assoc,
              pow_add, pow_succ, pow_two, mul_comm, mul_left_comm, mul_assoc]
      -- prove the rewritten expression is 0 modulo 13
      have hcongr :
          (16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) ≡ (0 : ℕ) [MOD 13] := by
        -- replace 16 by 3 modulo 13
        have hA :
            (16 * 4 ^ (2 * n + 1)) ≡ (3 * 4 ^ (2 * n + 1)) [MOD 13] :=
          (Nat.ModEq.mul_left (4 ^ (2 * n + 1)) h16).trans
            (by simpa [mul_comm, mul_left_comm, mul_assoc])
        have hB :
            (3 * 3 ^ (n + 2)) ≡ (3 * 3 ^ (n + 2)) [MOD 13] :=
          Nat.ModEq.rfl
        have hsum :
            (16 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) ≡
            (3 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) [MOD 13] :=
          Nat.ModEq.add hA hB
        have hfactor :
            (3 * 4 ^ (2 * n + 1) + 3 * 3 ^ (n + 2)) ≡
            3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) [MOD 13] := by
          simpa [mul_add, add_comm, add_left_comm, add_assoc,
                 mul_comm, mul_left_comm, mul_assoc] using (Nat.ModEq.rfl : _)
        have hzero :
            3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) ≡ (0 : ℕ) [MOD 13] :=
          (Nat.ModEq.mul_left 3 ih_mod)
        exact hsum.trans (hfactor.trans hzero)
      -- turn the congruence back into the original expression and finish
      have : (4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2)) ≡ (0 : ℕ) [MOD 13] := by
        simpa [hrew] using hcongr
      exact (Nat.ModEq.zero_iff_dvd).mp this
