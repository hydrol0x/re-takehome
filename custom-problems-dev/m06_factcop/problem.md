# m06_factcop

Prove that for every integer $n \ge 1$, the numbers $n! + 1$ and $(n+1)! + 1$
are coprime:
$$\gcd\bigl(n! + 1,\; (n+1)! + 1\bigr) = 1.$$

Prove the theorem `m06_factcop`. Key idea: any common divisor $d$ also divides
$(n+1)(n!+1) - \bigl((n+1)!+1\bigr) = n$, hence divides $n!$, hence divides
$(n!+1) - n! = 1$.
