# m07_sumgeo

Prove the arithmetico-geometric sum identity
$$\sum_{i=0}^{n-1} i \cdot 2^i = (n - 2)\,2^n + 2$$
for every natural number $n$, as an identity of integers.

Prove the theorem `m07_sumgeo` (the sum is over `Finset.range n` with integer
values, so the right-hand side may involve a negative factor for small $n$).
Induction on $n$ plus cast normalization and `ring` suffices.
