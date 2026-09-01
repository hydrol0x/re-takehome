import Mathlib

open scoped BigOperators

/-- `∑_{i=0}^{n-1} i * 2 ^ i = (n - 2) * 2 ^ n + 2` as integers. -/
theorem m07_sumgeo (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℤ) * 2 ^ i = ((n : ℤ) - 2) * 2 ^ n + 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (∑ i ∈ Finset.range (n + 1), (i : ℤ) * 2 ^ i)
            = (∑ i ∈ Finset.range n, (i : ℤ) * 2 ^ i) + (n : ℤ) * 2 ^ n := by
              simpa [Finset.sum_range_succ] using
                (Finset.sum_range_succ (fun i : ℕ => (i : ℤ) * 2 ^ i) n)
        _ = ((n : ℤ) - 2) * 2 ^ n + 2 + (n : ℤ) * 2 ^ n := by
              simpa [ih]
        _ = ((n + 1 : ℤ) - 2) * 2 ^ (n + 1) + 2 := by
              ring
