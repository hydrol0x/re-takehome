# m04_sumfact

Prove the telescoping factorial identity
$$\sum_{i=1}^{n} i \cdot i! = (n+1)! - 1$$
for every natural number $n$. (In the Lean statement the sum runs over
`i ∈ Finset.range n` with summand $(i+1)\cdot(i+1)!$.)

Prove the theorem `m04_sumfact`. Induction on $n$ works; note the subtraction
is natural-number subtraction, so it helps to move to `ℤ` (e.g. with `zify`)
using $(n+1)! \ge 1$.
