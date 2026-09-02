import Mathlib

/-- Key identity: (n+1)*(n!+1) = (n+1)! + 1 + n -/
lemma factcop_identity (n : ℕ) : 
    (n + 1) * (Nat.factorial n + 1) = Nat.factorial (n + 1) + 1 + n := by
  exact?

/-- For n ≥ 1, n divides n! -/
lemma n_divides_factorial (n : ℕ) (hn : 1 ≤ n) :
    n ∣ Nat.factorial n := by
  cases n with
  | zero => omega
  | succ m =>
    rw [Nat.factorial_succ]
    exact dvd_mul_right _ _

/-- If d divides both a and b, then d divides a - b when a ≥ b -/
lemma dvd_of_dvd_and_le {a b d : ℕ} (hab : b ≤ a) (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ a - b := by
  exact?

/-- The gcd of n!+1 and (n+1)!+1 divides n -/
lemma gcd_divides_n (n : ℕ) :
    Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) ∣ n := by
  have hg_l : Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) ∣ Nat.factorial n + 1 := Nat.gcd_dvd_left _ _
  have hg_r : Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) ∣ Nat.factorial (n + 1) + 1 := Nat.gcd_dvd_right _ _
  have hg_l2 : Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) ∣ (n + 1) * (Nat.factorial n + 1) := dvd_mul_of_dvd_right hg_l _
  have h_sum : Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) ∣ (Nat.factorial (n + 1) + 1) + n := by
    rw [← factcop_identity n]
    exact hg_l2
  have h_le : Nat.factorial (n + 1) + 1 ≤ (Nat.factorial (n + 1) + 1) + n := by
    apply Nat.le_add_right
  sorry

/-- If d divides n and d divides n!, then d divides 1 -/
lemma dvd_one_from_factorial {d n : ℕ} (hdn : d ∣ n) (hdnf : d ∣ Nat.factorial n) :
    d ∣ 1 := by
  sorry

/-- For n ≥ 1, n divides n! implies gcd(n!+1, (n+1)!+1) = 1 -/
lemma final_step (n : ℕ) (hn : 1 ≤ n) :
    Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) = 1 := by
  let g := Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1)
  have hg_dvd_n : g ∣ n := gcd_divides_n n
  have hn_dvd_fact : n ∣ Nat.factorial n := n_divides_factorial n hn
  have hg_dvd_fact : g ∣ Nat.factorial n := dvd_trans hg_dvd_n hn_dvd_fact
  have hg_dvd_one : g ∣ 1 := dvd_one_from_factorial hg_dvd_n hg_dvd_fact
  exact Nat.eq_one_of_dvd_one hg_dvd_one

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  exact?
