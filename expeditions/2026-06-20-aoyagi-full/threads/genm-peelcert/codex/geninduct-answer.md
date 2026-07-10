**Q1.** No, not in general. For
\[
\Phi:\Gamma\in\mathbb R^{a\times b},\quad Y\in\mathbb R^{b\times q}\mapsto Z=\Gamma Y\in\mathbb R^{a\times q},
\]
near a corank-\(j\) chart of \(\Gamma\),
\[
\Gamma\sim \begin{pmatrix}I&0\\0&E\end{pmatrix},\qquad
E\in\mathbb R^{j\times(b-a+j)}.
\]
The collapsing block has dimension
\[
d_j=j(b-a+j),
\]
and scales \(N_j=jq\) output coordinates. Radially,
\[
dE\sim r^{d_j-1}dr,\qquad EY\sim r(\cdots),
\]
so the pushforward density has model factor
\[
\int_{r\gtrsim |z|} r^{d_j-1-N_j}\,dr.
\]
Thus:

- \(d_j>N_j\), i.e. \(q<b-a+j\): bounded density.
- \(d_j=N_j\), i.e. \(q=b-a+j\): logarithmic density.
- \(d_j<N_j\), i.e. \(q>b-a+j\): genuine power
  \[
  |z|^{-(N_j-d_j)}=|z|^{-j(q-b+a-j)}.
  \]

So “bilinear pushforward is only logarithmic” is true only in balanced charts. For all corank strata to be sub-power one needs, in particular, \(q\le b-a+1\). The small case \(a=1,b=q=2\) is exactly logarithmic. Multilinear products inherit this chartwise: every multiplication step must satisfy the same dimension inequality; otherwise a power density can appear.

**Q2.** Conditional yes. If the bottom-block product map is dominant onto the relevant \(W\)-coordinates and its pushforward is bounded above and below by log-powers times Lebesgue measure, then
\[
\int \|WA\|^{-2s}\,d\mu(W)\,dA
\]
has the same RLCT as the flat integral with \(W\) free. Logs change only pole order, not the threshold, and dominance gives positive mass near the flat critical charts. Under that hypothesis the corner reduces to the shorter flat DLN chain, so arity induction gives \(\frac12\minAdm\) for that shorter chain.

Unconditionally, no: if Q1 is in a power regime, or the product map is not dominant, the constrained \(W\) need not have the flat-chain threshold.

**Q3.** The proportionality locus is genuinely part of the product-rank resolution in general width, though it may be hidden inside a flag/incidence resolution rather than named separately. After only \(A=0\), \(Y=0\), and \(\operatorname{im}A\subset\ker Y\), residual minors can still vanish because two pivot/tail column-pairs become dependent; those are determinantal rank-drop loci and must be resolved for normal crossings.

The statement that no resulting stratum has RLCT below \(\frac12\minAdm\) is not a consequence of Q1+Q2 alone. Q1+Q2 handle already-monomialized log-twist corners. They do not prove that all product-rank centers have been resolved, nor the exceptional-divisor Jacobian inequalities. That is precisely the Aoyagi §5 product-rank-flag content to import: the center list, chart splitting, Jacobian bookkeeping, and induction showing every remaining tail is a shorter admissible chain with divisor candidates \(\ge\frac12\minAdm\).