import Mathlib

open Finset

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  -- factor each term
  have h_factor :
      ∀ k ∈ Finset.Icc 2 n,
        ((1 : ℝ) - 1 / (k : ℝ) ^ 2) =
          ((k : ℝ) - 1) / k * ((k : ℝ) + 1) / k := by
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero k)
    field_simp [pow_two, hk0] ; ring
  -- split the product into two products
  have h_prod_eq :
      ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) =
        (∏ k ∈ Finset.Icc 2 n, ((k : ℝ) - 1) / k) *
        (∏ k ∈ Finset.Icc 2 n, ((k : ℝ) + 1) / k) := by
    have h1 :
        ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) =
          ∏ k ∈ Finset.Icc 2 n, ((k : ℝ) - 1) / k * ((k : ℝ) + 1) / k := by
      apply Finset.prod_congr rfl
      intro k hk
      exact (h_factor k hk).symm
    have h2 :
        ∏ k ∈ Finset.Icc 2 n, ((k : ℝ) - 1) / k * ((k : ℝ) + 1) / k =
          (∏ k ∈ Finset.Icc 2 n, ((k : ℝ) - 1) / k) *
          (∏ k ∈ Finset.Icc 2 n, ((k : ℝ) + 1) / k) := by
      simpa using
        (Finset.prod_mul_distrib
          (s := Finset.Icc 2 n)
          (f := fun k => ((k : ℝ) - 1) / k)
          (g := fun k => ((k : ℝ) + 1) / k))
    simpa [h1] using h2
  -- evaluate the first product
  have h_sub :
      (∏ k ∈ Finset.Icc 2 n, ((k : ℝ) - 1) / k) = (1 : ℝ) / n := by
    have : ∀ m, 2 ≤ m → (∏ k ∈ Finset.Icc 2 m, ((k : ℝ) - 1) / k) = (1 : ℝ) / m := by
      intro m
      apply Nat.le_induction
      · intro hm
        have : (∏ k ∈ Finset.Icc 2 2, ((k : ℝ) - 1) / k) = ((2 : ℝ) - 1) / 2 := by
          simp
        simpa using this
      · intro m hm ih hle
        have hprod :=
          (Finset.prod_Icc_succ_top
            (a := 2) (b := m)
            (f := fun k : ℕ => ((k : ℝ) - 1) / k) hm)
        calc
          (∏ k ∈ Finset.Icc 2 (m + 1), ((k : ℝ) - 1) / k)
              = (∏ k ∈ Finset.Icc 2 m, ((k : ℝ) - 1) / k) *
                ((m + 1 : ℝ) - 1) / (m + 1) := by
                simpa using hprod
          _ = (1 / (m : ℝ)) * ((m + 1 : ℝ) - 1) / (m + 1) := by
                simpa [ih]
          _ = (1 / (m : ℝ)) * (m : ℝ) / (m + 1) := by
                simp
          _ = (1 : ℝ) / (m + 1) := by
                field_simp
    exact this n hn
  -- evaluate the second product
  have h_add :
      (∏ k ∈ Finset.Icc 2 n, ((k : ℝ) + 1) / k) = ((n : ℝ) + 1) / 2 := by
    have : ∀ m,
