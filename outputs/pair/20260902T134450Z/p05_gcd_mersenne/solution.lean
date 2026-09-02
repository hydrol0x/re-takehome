import Mathlib

/-- What is the greatest common divisor of `2 ^ 1001 - 1` and `2 ^ 1012 - 1`?
Show that it is `2 ^ 11 - 1`. -/
theorem p05_gcd_mersenne :
    Nat.gcd (2 ^ 1001 - 1) (2 ^ 1012 - 1) = 2 ^ 11 - 1 := by
  calc
    Nat.gcd (2 ^ 1001 - 1) (2 ^ 1012 - 1)
        = 2 ^ Nat.gcd 1001 1012 - 1 := by
          simpa [one_pow] using
            (Nat.gcd_pow_left_sub_pow_right (a := 2) (b := 1) (m := 1001) (n := 1012))
    _ = 2 ^ 11 - 1 := by
          norm_num
