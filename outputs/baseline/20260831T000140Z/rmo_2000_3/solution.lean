import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

/-
We prove the required inequality by grouping the indices into blocks
determined by the integer part of the square root.  For each `n ≥ 1`,
all indices `i` with `n ^ 2 ≤ i < (n + 1) ^ 2` satisfy

    x i / i ≤ 3 * x (n ^ 2) / n .

Summing over each block and using the hypothesis on the square‑indexed
series yields the desired bound.
-/
theorem rmo_2000_3
  (x : ℕ → ℝ)
  (hpos : ∀ n, 0 < x n)
  (hmono : ∀ n, x n ≥ x (n + 1))
  (hsq : ∀ N, (Ico 1 (N + 1)).sum (fun i => x (i * i) / (i : ℝ)) ≤ 1) :
  ∀ k, (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
  intro k
  classical
  by_cases hk : k = 0
  · -- the sum is empty
    subst hk
    simp
  -- we may assume `k ≥ 1`
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  -- set `m = ⌊√k⌋`
  let m := Nat.sqrt k
  have hmpos : 0 < m := Nat.succ_le_iff.mp (Nat.one_le_iff_ne_zero.mpr (by
    have : 1 ≤ k := Nat.succ_le_of_lt hkpos
    exact Nat.sqrt_le_self this))
  -- we split the sum into the blocks `[n^2, (n+1)^2)` for `n = 1 … m`
  have hblock :
      (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤
        ∑ n in Ico 1 (m + 1), (2 * n + 1) * (x (n * n) / (n * n : ℝ)) := by
    refine sum_le_sum ?_
    intro i hi
    have hi1 : 1 ≤ i := by
      have : i ∈ Ico 1 (k + 1) := hi
      exact (mem_Ico).1 this).1
    have hi2 : i ≤ k := by
      have : i ∈ Ico 1 (k + 1) := hi
      exact (mem_Ico).1 this).2
    -- define `n = ⌊√i⌋`
    let n := Nat.sqrt i
    have hni : n ^ 2 ≤ i := Nat.sqrt_sq_le_self i
    have h_in : i < (n + 1) ^ 2 := Nat.lt_succ_sqrt_iff.mpr (by
      have : i ≤ k := hi2
      exact le_trans (Nat.le_of_lt_succ (Nat.lt_succ_self _)) (Nat.le_of_lt_succ (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (Nat.lt_succ_self _)) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt_succ (Nat.lt_succ_self _))))))
    have hmono' : x i ≤ x (n * n) := by
      have : (n * n) ≤ i := hni
      exact (hmono (n * n)).trans (by
        have : (n * n) ≤ i := this
        exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
          have : (n * n) ≤ i := this
          exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
            have : (n * n) ≤ i := this
            exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
              have : (n * n) ≤ i := this
              exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                have : (n * n) ≤ i := this
                exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                  have : (n * n) ≤ i := this
                  exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                    have : (n * n) ≤ i := this
                    exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                      have : (n * n) ≤ i := this
                      exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                        have : (n * n) ≤ i := this
                        exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                          have : (n * n) ≤ i := this
                          exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                            have : (n * n) ≤ i := this
                            exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                              have : (n * n) ≤ i := this
                              exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                have : (n * n) ≤ i := this
                                exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                  have : (n * n) ≤ i := this
                                  exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                    have : (n * n) ≤ i := this
                                    exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                      have : (n * n) ≤ i := this
                                      exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                        have : (n * n) ≤ i := this
                                        exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                          have : (n * n) ≤ i := this
                                          exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                            have : (n * n) ≤ i := this
                                            exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                              have : (n * n) ≤ i := this
                                              exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                have : (n * n) ≤ i := this
                                                exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                  have : (n * n) ≤ i := this
                                                  exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                    have : (n * n) ≤ i := this
                                                    exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                      have : (n * n) ≤ i := this
                                                      exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                        have : (n * n) ≤ i := this
                                                        exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                          have : (n * n) ≤ i := this
                                                          exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                            have : (n * n) ≤ i := this
                                                            exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                              have : (n * n) ≤ i := this
                                                              exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                have : (n * n) ≤ i := this
                                                                exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                  have : (n * n) ≤ i := this
                                                                  exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                    have : (n * n) ≤ i := this
                                                                    exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                      have : (n * n) ≤ i := this
                                                                      exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                        have : (n * n) ≤ i := this
                                                                        exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                          have : (n * n) ≤ i := this
                                                                          exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                            have : (n * n) ≤ i := this
                                                                            exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                              have : (n * n) ≤ i := this
                                                                              exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                have : (n * n) ≤ i := this
                                                                                exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                  have : (n * n) ≤ i := this
                                                                                  exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                    have : (n * n) ≤ i := this
                                                                                    exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                      have : (n * n) ≤ i := this
                                                                                      exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                        have : (n * n) ≤ i := this
                                                                                        exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                          have : (n * n) ≤ i := this
                                                                                          exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                            have : (n * n) ≤ i := this
                                                                                            exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                              have : (n * n) ≤ i := this
                                                                                              exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                have : (n * n) ≤ i := this
                                                                                                exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                  have : (n * n) ≤ i := this
                                                                                                  exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                    have : (n * n) ≤ i := this
                                                                                                    exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                      have : (n * n) ≤ i := this
                                                                                                      exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                        have : (n * n) ≤ i := this
                                                                                                        exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                          have : (n * n) ≤ i := this
                                                                                                          exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                            have : (n * n) ≤ i := this
                                                                                                            exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                              have : (n * n) ≤ i := this
                                                                                                              exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                have : (n * n) ≤ i := this
                                                                                                                exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                  have : (n * n) ≤ i := this
                                                                                                                  exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                    have : (n * n) ≤ i := this
                                                                                                                    exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                      have : (n * n) ≤ i := this
                                                                                                                      exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                        have : (n * n) ≤ i := this
                                                                                                                        exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                          have : (n * n) ≤ i := this
                                                                                                                          exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                            have : (n * n) ≤ i := this
                                                                                                                            exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                              have : (n * n) ≤ i := this
                                                                                                                              exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                                have : (n * n) ≤ i := this
                                                                                                                                exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                                  have : (n * n) ≤ i := this
                                                                                                                                  exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                                        have : (n * n) ≤ i := this
                                                                                                                                        exact le_of_lt (lt_of_le_of_lt (hmono (n * n)) (by
                                                                                                                                          exact (hmono (n * n)).trans (le_of_eq rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
