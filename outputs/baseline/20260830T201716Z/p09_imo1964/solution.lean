lemma pow_two_mod_three (n : ℕ) : (2 ^ n) % 7 = match n % 3 with
  | 0 => 1
  | 1 => 2
  | 2 => 4
end := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> simp [Nat.add_mod, Nat.mul_mod]
    <;> norm_num
    <;> omega
