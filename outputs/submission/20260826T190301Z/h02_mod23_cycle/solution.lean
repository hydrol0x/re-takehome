import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq

/-- (a): 2^11 ≡ 1 (mod 23) -/
lemma pow2_11_mod23 : 2 ^ 11 % 23 = 1 := by norm_num

/-- (a): 2^n ≡ 1 (mod 23) implies 11 ∣ n -/
lemma pow2_eq_one_implies_div11 (n : ℕ) (h : 2 ^ n % 23 = 1) : 11 ∣ n := by sorry

/-- (a): 11 ∣ n implies 2^n ≡ 1 (mod 23) -/
lemma div11_implies_pow2_eq_one (n : ℕ) (h : 11 ∣ n) : 2 ^ n % 23 = 1 := by sorry

/-- (b): 2^n ≢ -1 (mod 23) for any n -/
lemma pow2_neq_neg1_mod23 (n : ℕ) : 2 ^ n % 23 ≠ 22 := by sorry

/-- (a): 23 ∣ 2^n - 1 ↔ 2^n ≡ 1 (mod 23) -/
lemma dvd_sub_one_iff_mod_eq_one (n : ℕ) : 23 ∣ 2 ^ n - 1 ↔ 2 ^ n % 23 = 1 := by sorry

/-- (b): 23 ∣ 2^n + 1 ↔ 2^n ≡ -1 (mod 23) -/
lemma dvd_add_one_iff_mod_eq_neg_one (n : ℕ) : 23 ∣ 2 ^ n + 1 ↔ 2 ^ n % 23 = 22 := by omega

/-- Main theorem (a): 23 ∣ 2^n - 1 iff 11 ∣ n, for positive n -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  calc
      23 ∣ 2 ^ n - 1 ↔ 2 ^ n % 23 = 1 := dvd_sub_one_iff_mod_eq_one n
      _ ↔ 11 ∣ n := by
        constructor
        · intro h
          exact pow2_eq_one_implies_div11 n h
        · intro h
          exact div11_implies_pow2_eq_one n h

/-- Main theorem (b): no positive n has 23 ∣ 2^n + 1 -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  sorry
