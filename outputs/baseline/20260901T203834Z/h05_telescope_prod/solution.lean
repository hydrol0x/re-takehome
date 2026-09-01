import Mathlib

open Finset
open Nat

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  -- rewrite each factor
  have h_factor (k : ℕ) :
      (1 : ℝ) - 1 / (k : ℝ) ^ 2 = ((k : ℝ) - 1) / k * ((k : ℝ) + 1) / k := by
    field_simp [pow_two] ; ring
  -- replace the product by a product of two simpler products
  have h_prod :
      ∏ k ∈ Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) =
        (∏ k ∈ Icc 2 n, ((k : ℝ) - 1) / k) *
        (∏ k ∈ Icc 2 n, ((k : ℝ) + 1) / k) := by
    calc
      ∏ k ∈ Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2)
          = ∏ k ∈ Icc 2 n, (((k : ℝ) - 1) / k * ((k : ℝ) + 1) / k) := by
            apply prod_congr rfl
            intro k hk
            simpa [h_factor k]
      _ = (∏ k ∈ Icc 2 n, ((k : ℝ) - 1) / k) *
          (∏ k ∈ Icc 2 n, ((k : ℝ) + 1) / k) := by
            simpa using prod_mul_distrib (s := Icc 2 n)
              (f := fun k => ((k : ℝ) - 1) / k) (g := fun k => ((k : ℝ) + 1) / k)
  -- evaluate the first product
  have h_left : ∏ k ∈ Icc 2 n, ((k : ℝ) - 1) / k = (1 : ℝ) / (n : ℝ) := by
    have h₁ :
        (∏ k ∈ Icc 2 n, ((k : ℝ) - 1) / k) =
          (∏ k ∈ Icc 2 n, ((k : ℝ) - 1)) *
          (∏ k ∈ Icc 2 n, (k : ℝ)⁻¹) := by
        simpa [div_eq_mul_inv] using
          prod_mul_distrib (s := Icc 2 n)
            (f := fun k => ((k : ℝ) - 1)) (g := fun k => (k : ℝ)⁻¹)
    have hnum :
        (∏ k ∈ Icc 2 n, ((k : ℝ) - 1)) = ∏ k ∈ Icc 1 (n - 1), (k : ℝ) := by
      have : (∏ k ∈ Icc 2 n, (k - 1)) = ∏ k ∈ Icc 1 (n - 1), k := by
        refine (prod_Icc_eq_prod_range_succ (f := fun k => k - 1) (a := 2) (b := n)).trans ?_
        simp [Nat.succ_sub_one, Nat.sub_self, Nat.sub_eq_iff_eq_add] 
      simpa [Nat.cast_prod] using congrArg (fun x : ℕ => (x : ℝ)) this
    have hden :
        (∏ k ∈ Icc 2 n, (k : ℝ)⁻¹) = ((∏ k ∈ Icc 2 n, (k : ℝ)) )⁻¹ := by
      simpa using (Finset.inv_prod (s := Icc 2 n) (f := fun k => (k : ℝ)))
    have hnum' : (∏ k ∈ Icc 1 (n - 1), (k : ℝ)) = ((n - 1) ! : ℝ) := by
      simpa [Nat.cast_factorial] using
        (Nat.cast_prod (fun k => k) (Finset.Icc 1 (n - 1))).symm
    have hden' : (∏ k ∈ Icc 2 n, (k : ℝ)) = (n ! : ℝ) := by
      simpa [Nat.cast_factorial] using
        (Nat.cast_prod (fun k => k) (Finset.Icc 2 n)).symm
    have : (∏ k ∈ Icc 2 n, ((k : ℝ) - 1) / k) =
        ((n - 1)! : ℝ) * ((n! : ℝ) )⁻¹ := by
      simpa [h₁, hnum, hden, hnum', hden'] using rfl
    simpa [Nat.factorial_succ, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
  -- evaluate the second product
  have h_right : ∏ k ∈ Icc 2 n, ((k : ℝ) + 1) / k = ((n : ℝ) + 1) / 2 := by
    have h₁ :
        (∏ k ∈ Icc 2 n, ((k : ℝ) + 1) / k) =
          (∏ k ∈ Icc 2 n, ((k : ℝ) + 1)) *
          (∏ k ∈ Icc 2 n, (k : ℝ)⁻¹) := by
        simpa [div_eq_mul_inv] using
          prod_mul_distrib (s := Icc 2 n)
            (f := fun k => ((k : ℝ) + 1)) (g := fun k => (k : ℝ)⁻¹)
    have hnum :
        (∏ k ∈ Icc 2 n, ((k : ℝ) + 1)) = ∏ k ∈ Icc 3 (n + 1), (k : ℝ) := by
      have : (∏ k ∈ Icc 2 n, (k + 1)) = ∏ k ∈ Icc 3 (n + 1), k := by
        refine (prod_Icc_eq_prod_range_succ (f := fun k => k + 1) (a := 2) (b := n)).trans ?_
        simp [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      simpa [Nat.cast_prod] using congrArg (fun x : ℕ => (x : ℝ)) this
    have hden :
        (∏ k ∈ Icc 2 n, (k : ℝ)⁻¹) = ((∏ k ∈ Icc 2 n, (k : ℝ)) )⁻¹ := by
      simpa using (Finset.inv_prod (s := Icc 2 n) (f := fun k => (k : ℝ)))
    have hnum' : (∏ k ∈ Icc 3 (n + 1), (k : ℝ)) = ((n + 1)! : ℝ) / 2 := by
      have : (∏ k ∈ Icc 1 (n + 1), (k : ℝ)) = ((n + 1)! : ℝ) := by
        simpa [Nat.cast_factorial] using
          (Nat.cast_prod (fun k => k) (Finset.Icc 1 (n + 1))).symm
      have h2 : (∏ k ∈ Icc 3 (n + 1), (k : ℝ)) =
          ((∏ k ∈ Icc 1 (n + 1), (k : ℝ)) ) / (1 * 2) := by
        have : (∏ k ∈ Icc 1 (n + 1), (k : ℝ)) =
            (∏ k ∈ Icc 1 2, (k : ℝ)) * (∏ k ∈ Icc 3 (n + 1), (k : ℝ)) := by
          simpa [Finset.Icc_succ_left, Finset.Icc_succ_right, mul_comm, mul_left_comm,
                mul_assoc] using
            (Finset.prod_Icc_mul_eq_prod_Icc (a := 1) (b := 2) (c := n + 1)
              (f := fun k => (k : ℝ))).symm
        have h12 : (∏ k ∈ Icc 1 2, (k : ℝ)) = (1 : ℝ) * 2 := by
          simp
        have : (∏ k ∈ Icc 3 (n + 1), (k : ℝ)) =
            ((∏ k ∈ Icc 1 (n + 1), (k : ℝ)) ) / ((1 : ℝ) * 2) := by
          field_simp [h12] at *
        simpa using this
      simpa [this, Nat.cast_mul, Nat.cast_two] using h2
    have hden' : (∏ k ∈ Icc 2 n, (k : ℝ)) = (n ! : ℝ) := by
      simpa [Nat.cast_factorial] using
        (Nat.cast_prod (fun k => k) (Finset.Icc 2 n)).symm
    have : (∏ k ∈ Icc 2 n, ((k : ℝ) + 1) / k) =
        ((n + 1)! : ℝ) / 2 * ((n ! : ℝ) )⁻¹ := by
      simpa [h₁, hnum, hden, hnum', hden'] using rfl
    have : ((n + 1)! : ℝ) / (2 * (n ! : ℝ)) = ((n : ℝ) + 1) / 2 := by
      have : ((n + 1)! : ℝ) = (n + 1 : ℝ) * (n ! : ℝ) := by
        simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.factorial_succ] using rfl
      field_simp [this, Nat.cast_two] ; ring
    simpa [this] using this
  -- combine the two evaluated products
  have : ∏ k ∈ Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) =
      ((1 : ℝ) / (n : ℝ)) * (((n : ℝ) + 1) / 2) := by
    simpa [h_left, h_right] using h_prod
  simpa [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using this
