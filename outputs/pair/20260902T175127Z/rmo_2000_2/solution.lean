lemma sub_valid (x : ℕ) (hx : 0 < x) : x ^ 3 + 8 * x ^ 2 + 8 ≥ 6 * x := by
  have h : x ≥ 1 := by omega
  have h2 : x ^ 3 + 8 * x ^ 2 + 8 ≥ 6 * x := by
    induction' h with x h IH
    · norm_num
    · cases x with
      | zero => contradiction
      | succ x' =>
        simp_all [Nat.succ_mul, Nat.mul_succ]
        nlinarith
  exact h2
