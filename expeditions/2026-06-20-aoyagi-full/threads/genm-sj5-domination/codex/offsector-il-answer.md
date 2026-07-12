Q1. Yes, with qualifications.

For \(b=1\),
\[
\int |A_{\rm cor}Z|^{-a}\,dA_{\rm cor}
\]
is finite iff \(a<M_2\); hence the untruncated atom cannot dominate the off sector when \(a\ge M_2\). The bounded brick remains finite pointwise in \(A_{\rm cor}\).

Fact 1 is correct. Fact 2 is correct in the centred case and for \(c'>a/2\); with an offset \(c_0\), the limit is \((w+\|c_0\|^2)^{-c'}\operatorname{vol}\), and the transformed domain is a translated parallelepiped, not literally a centred box.

Q2. For \(b=1\), it closes. Put
\[
R_s=\minAdm(s,M_2,\ldots),\qquad r=\sqrt w.
\]
Binding at \(t\) gives
\[
a+R_t\le R_{t+1}.
\]
Also \(R_{t+1}\le R_t+M_2\), hence \(a\le M_2\).

On a uniformly full-rank tail chart,
\[
\operatorname{vol}\{\|A_{\rm cor}Z\|\le r\}\lesssim r^{M_2},
\]
so the bounded contribution is
\[
w^{-c'}r^{M_2}=w^{-(c'-M_2/2)}.
\]
Since
\[
c'<\frac{a+R_t}{2}
\quad\Longrightarrow\quad
c'-\frac{M_2}{2}<\frac{R_t}{2},
\]
the reduced IH closes it. The atom gives \(w^{-(c'-a/2)}\), also inside the IH range. At \(a=M_2\) one gets only an extra logarithm, harmless under the strict inequality.

More generally, on a tail rank-\(\rho\) chart of charge \(D_\rho\),
\[
D_\rho+(t+1)\rho\ge R_{t+1}\ge R_t+a,
\]
so tail degeneration supplies exactly the missing measure charge.

For \(b>1\), the literal split at \(\sigma_{\min}(Q_b)=r\) is too crude. Example: \(M=(3,3,3)\), \(t=1\), \(a=b=2\). Using the bounded brick on all \(\{\sigma_2(Q)\le r\}\) gives only
\[
\frac{3+2}{2}=\frac52<\frac72=\frac12\minAdm(M).
\]
But the exact minimum does close: its switch is \(\tau_1\tau_2\asymp r^2\), not \(\tau_2\asymp r\), producing \(r^{4-2c'}\log(1/r)\) and threshold \(7/2\).

Thus \(b>1\) requires the full singular-flag regimes. Their charges are
\[
C_j=(a-j)(b-j)+R_{t+j}\ge ab+R_t=\minAdm(M),
\]
directly from binding. No width undershoots.

Q3. Yes, with adapted rank charts. For \(Z=xy\), peeling one factor sends the bad point \(x=y=0\) to the shorter tail \(y=0\), which is then the free one-layer base.

At that base, “order one everywhere” must mean transverse-normal order, not order along every curve. On a rank chart the normal coordinate is the Schur complement
\[
S=D-CP^{-1}B,\qquad \partial S/\partial D=I.
\]
For \(M(t)=\begin{psmallmatrix}1&t\\t&0\end{psmallmatrix}\), the constrained curve has \(S=-t^2\), but in the full free matrix space \(S=D-t^2\), so the free \(D\)-direction is first order. Finite rank stratification handles deeper coranks.

This requires uniform adapted pivot charts and their measure bounds; depth decrease alone is not a proof of those estimates.

Q4. **CLOSES (labour)** — for the exact-min/singular-flag version; the literal \(b>1\) \(\sigma_{\min}\)-only split does not.

Fact 3 is correct for \(b=1\). Fact 4’s examples are correct, but at a binding \(b=1\) cut one always has \(a\le M_2\), so only equality—not \(a>M_2\)—can occur; \((3,3,4)\) is not atom-divergent since \(2<M_2-b+1=3\).