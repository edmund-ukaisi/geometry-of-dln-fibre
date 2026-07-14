## VERDICT: TRUE

### FACT — exhaustive sweep

Domain: every \(M\in\{1,\ldots,7\}^n\), \(n=4,5,6\), filtered to GOOD chains with genuine, non-empty \(j=0\) sector shells.

| Arity | Eligible chains | \(a^*+b^*\le M_2\) | \(a^*+b^*=M_2+1\) | \(a^*+b^*\ge M_2+2\) |
|---:|---:|---:|---:|---:|
| 4 | 352 | 330 | 22 | **0** |
| 5 | 1,900 | 1,830 | 70 | **0** |
| 6 | 9,859 | 9,597 | 262 | **0** |
| **Total** | **12,111** | **11,757** | **354** | **0** |

Two independent exact-integer implementations—recursive memoization and bottom-up suffix DP—gave identical counts.

### INFERENCE — mechanism

Let
\[
G(x)=\operatorname{minAdm}\bigl((x,M_2,\ldots,M_{\mathrm{last}})\bigr).
\]
Reusing a minimizing first cut for \(G(x)\) at \(x+1\) gives
\[
G(x+1)-G(x)\le M_2.
\]

At a genuine binding corner, \(t^*+1\) is feasible. Optimality of \(t^*\) therefore gives
\[
a^*b^*+G(t^*)
 \le (a^*-1)(b^*-1)+G(t^*+1),
\]
hence
\[
a^*+b^*
 \le 1+G(t^*+1)-G(t^*)
 \le M_2+1.
\]

Thus the third bucket is impossible for **all widths and arities**, not merely this sweep. GOOD and sector non-emptiness are not needed beyond genuineness.

## Balanced cubes

Every listed cube is GOOD with a genuine, non-empty shell.

| Arity | \(w\) | \(t^*\) | \(a^*+b^*\) | bound \(w\) | hcvg? |
|---:|---:|---:|---:|---:|:---:|
| 4 | 2 | 1 | 2 | 2 | Yes |
| 4 | 3 | 2 | 2 | 3 | Yes |
| 4 | 4 | 2 | 4 | 4 | Yes |
| 4 | 5 | 3 | 4 | 5 | Yes |
| 4 | 6 | 4 | 4 | 6 | Yes |
| 4 | 7 | 4 | 6 | 7 | Yes |
| 5 | 2 | 1 | 2 | 2 | Yes |
| 5 | 3 | 2 | 2 | 3 | Yes |
| 5 | 4 | 3 | 2 | 4 | Yes |
| 5 | 5 | 3 | 4 | 5 | Yes |
| 5 | 6 | 4 | 4 | 6 | Yes |
| 5 | 7 | 5 | 4 | 7 | Yes |
| 6 | 2 | 1 | 2 | 2 | Yes |
| 6 | 3 | 2 | 2 | 3 | Yes |
| 6 | 4 | 3 | 2 | 4 | Yes |
| 6 | 5 | 4 | 2 | 5 | Yes |
| 6 | 6 | 4 | 4 | 6 | Yes |
| 6 | 7 | 5 | 4 | 7 | Yes |