# Verdict: FALSE

The obstruction occurs exclusively at \(j=0\). For every \(j\ge1\), the implication is true.

## FACT — smallest counterexample

Take

\[
M=(2,2,1).
\]

The three cut values are

\[
\begin{array}{c|ccc}
u&0&1&2\\ \hline
(2-u)^2+\minAdm(u,1)&4&2&2.
\end{array}
\]

Thus the least achiever is \(t^*=1\), and \(r=1\).

At \(j=0\):

\[
u=1,\qquad a=1,\qquad b=1,\qquad m=\min(2,1)=1.
\]

Moreover,

\[
\operatorname{hrange}:1\le M_2=1,
\]
\[
\operatorname{hpiv}:\minAdm(1,1)=1\le1\cdot\min(2,1)=1,
\]

but

\[
a+b=2>1=m.
\]

The only other shell, \(j=1\), has \(a=b=0\), so it is not genuine. Hence \(M\) is GOOD but violates `hcvg`.

This is componentwise smallest: a genuine shell with \(t^*\ge1\) requires \(M_0,M_1\ge2\), while positivity requires \(M_2\ge1\).

## FACT — exhaustive counts

Each row sweeps the full width cube.

| Widths | Arity | Chains | GOOD chains | \(j=0\) shells (fail) | \(j\ge1\) shells (fail) |
|---|---:|---:|---:|---:|---:|
| \(1..7\) | 3 | 343 | 211 | 99 (57) | 54 (0) |
| \(1..7\) | 4 | 2,401 | 1,906 | 352 (124) | 117 (0) |
| \(1..7\) | 5 | 16,807 | 14,644 | 1,900 (462) | 341 (0) |
| **\(1..7\)** | **total** | **19,551** | **16,761** | **2,351 (643)** | **512 (0)** |
| \(1..8\) | 3 | 512 | 314 | 146 (82) | 96 (0) |
| \(1..8\) | 4 | 4,096 | 3,257 | 586 (198) | 251 (0) |
| \(1..8\) | 5 | 32,768 | 28,618 | 3,631 (840) | 873 (0) |
| **\(1..8\)** | **total** | **37,376** | **32,189** | **4,363 (1,120)** | **1,220 (0)** |

Every failure-bearing GOOD chain had failure set exactly \(\{0\}\): failures are not scattered. Counting `hpiv` shell-locally instead of imposing global GOOD gives the same failure counts.

## INFERENCE — why \(j\ge1\) differs

Put

\[
D(x)=\minAdm((x,)+M[2:]),\qquad
w=\operatorname{tailMinWidth}(M),\qquad
q=\min(M_1,M_{\rm last}).
\]

The recursion makes \(D\) discretely concave with \(D(0)=0\); hence, for \(0<t<u\),

\[
uD(t)\ge tD(u).
\]

Binding minimality, with \(u=t+j\), gives

\[
j(a+b+j)\le D(u)-D(t).
\]

Using concavity and `hpiv`,

\[
D(u)-D(t)\le \frac{j}{u}D(u)\le jw\le jq.
\]

For \(j\ge1\), cancellation yields

\[
a+b+j\le q,
\]

so \(m=q-j\) and therefore \(a+b\le m\).

At \(j=0\), the binding inequality degenerates to \(0\le0\), providing no control over \(a+b\). The least-achiever tie in \((2,2,1)\) exposes exactly this missing endpoint constraint.