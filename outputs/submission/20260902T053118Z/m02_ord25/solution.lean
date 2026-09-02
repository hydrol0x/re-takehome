import Mathlib

/-- The least positive integer `n` such that `2 ^ n` leaves remainder `1` when
divided by `25`. Must be a numeric literal. -/
abbrev m02_answer : ℕ := 20

/-- `m02_answer` is the least element of the set of positive `n` with
`2 ^ n % 25 = 1`; that is, the multiplicative order of `2` modulo `25`. -/
theorem m02_ord25 : IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 25 = 1} m02_answer := by
  constructor
  · -- Prove that m02_answer is in the set (i.e., 0 < 20 and 2^20 % 25 = 1)
    constructor
    · -- Prove 0 < 20
      decide
    · -- Prove 2^20 % 25 = 1
      norm_num [Nat.pow_mod]
  · -- Prove that m02_answer is the least element (no smaller positive n works)
    intro n hn
    simp only [Set.mem_setOf_eq, Nat.succ_le_iff, Prod.mk.injEq, Nat.zero_lt_succ] at hn
    cases' hn with hpos heq
    by_contra hlt
    -- If n < 20, then 2^n % 25 ≠ 1
    have hne : 2 ^ n % 25 ≠ 1 := by
      -- Check all values from 1 to 19
      interval_cases n <;> norm_num [Nat.pow_mod] at * <;> try contradiction
    exact hne (by simpa [heq] using congrArg (fun x => x % 25) (by omega))
