import Mathlib

def S (k : ℕ) : ℕ := ∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j

-- Lemma stating the base case
lemma S_base : S 0 = 1 := by
  simp [S]
  <;> decide

-- Lemma stating the recurrence relation
lemma S_step (k : ℕ) : S (k + 1) = 4 * S k := by sorry

-- Helper lemma linking S to the power of 4 using induction
theorem S_eq_pow (k : ℕ) : S k = 4 ^ k := by
  induction k with
  | zero =>
    rw [S_base]
    <;> norm_num
  | succ k ih =>
    rw [S_step, pow_succ]
    -- Using commutativity to match 4 * 4^k with 4^(k+1)
    <;> ring_nf at *
    <;> linarith

theorem putnam_2020_a2
  (k : ℕ) :
  (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k := by
  -- Rewrite the sum in the goal to use our defined function S
  rw [show ∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j = S k by rfl]
  -- Use the helper lemma S_eq_pow which connects S k to 4^k
  exact S_eq_pow k
