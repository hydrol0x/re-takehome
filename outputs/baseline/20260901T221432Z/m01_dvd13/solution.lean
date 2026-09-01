import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  induction n with
  | zero =>
      -- base case: 4 + 9 = 13
      have h : (4 ^ (2 * 0 + 1) + 3 ^ (0 + 2)) % 13 = 0 := by
        norm_num
      exact (Nat.dvd_iff_mod_eq_zero).mpr h
  | succ n ih =>
      -- induction hypothesis as a mod‑equality
      have ih_mod : (4 ^ (2 * n + 1) + 3 ^ (n + 2)) % 13 = 0 :=
        (Nat.dvd_iff_mod_eq_zero).mp ih
      -- rewrite the expression for `n+1`
      have hrew :
          (4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2)) =
            4 ^ (2 * n + 1) * 16 + 3 ^ (n + 2) * 3 := by
        have h1 : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by
          ring
        have h2 : (n + 1) + 2 = (n + 2) + 1 := by
          ring
        simp [h1, h2, Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      -- 16 ≡ 3 (mod 13)
      have h16 : (16 : ℕ) ≡ 3 [MOD 13] := by
        unfold Nat.ModEq
        norm_num
      -- replace 16 by 3 in the left‑hand side, keep the right term unchanged
      have hmod1 :
          (4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2)) ≡
            3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) [MOD 13] := by
        have hA : (4 ^ (2 * n + 1) * 16) ≡ (4 ^ (2 * n + 1) * 3) [MOD 13] :=
          h16.mul_left _
        have hB : (3 ^ (n + 2) * 3) ≡ (3 ^ (n + 2) * 3) [MOD 13] :=
          Nat.ModEq.refl _
        have hC := hA.add hB
        simpa [hrew, mul_comm, mul_left_comm, mul_assoc,
               left_distrib, right_distrib, add_comm, add_left_comm, add_assoc,
               mul_add, add_mul] using hC
      -- from the induction hypothesis we have a congruence to 0
      have hzero : (4 ^ (2 * n + 1) + 3 ^ (n + 2)) ≡ 0 [MOD 13] := by
        unfold Nat.ModEq
        simpa using ih_mod
      have hzero3 : 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) ≡ 0 [MOD 13] :=
        hzero.mul_left 3
      have hfinal :
          (4 ^ (2 * (n + 1) + 1) + 3 ^ ((n + 1) + 2)) ≡ 0 [MOD 13] :=
        hmod1.trans hzero3
      exact (Nat.dvd_iff_mod_eq_zero).mpr (by
        simpa [Nat.ModEq] using hfinal)
