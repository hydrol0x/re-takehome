# m02_ord25

Find the least positive integer $n$ such that $2^n \equiv 1 \pmod{25}$, i.e.
the multiplicative order of $2$ modulo $25$.

Fill in `m02_answer` with a numeric literal and prove the theorem `m02_ord25`.
`IsLeast S a` means `a ∈ S` and `a` is a lower bound of `S`, so the proof has
two parts: your $n$ satisfies $2^n \bmod 25 = 1$, and no smaller positive
exponent does.
