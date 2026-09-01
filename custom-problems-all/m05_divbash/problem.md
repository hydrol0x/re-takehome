# m05_divbash

Find all positive integers $n$ such that $n + 2$ divides $n^2 + 4$. Show that
the answer is exactly $n = 2$ and $n = 6$.

Prove the theorem `m05_divbash` (an iff). For the forward direction, from
$(n+2) \mid n^2 + 4$ and $(n+2) \mid (n+2)^2 = n^2 + 4n + 4$ deduce
$(n+2) \mid 4n$ and then $(n+2) \mid 8$, which bounds $n \le 6$; a finite check
finishes.
