Write \(e_k=\mathrm{divExp}_k\). For \(B=\operatorname{blowup}(C,p)\circ\operatorname{swap}(p,d)\), the relevant coordinate pullbacks are

\[
z_c(B(w))=
\begin{cases}
z_c(w),&c\notin C,\\
z_d(w),&c=p,\\
z_d(w)z_p(w),&c=d\ne p,\\
z_d(w)z_c(w),&c\in C\setminus\{p,d\}.
\end{cases}
\]

If \(p=d\), then \(z_d(B(w))=z_d(w)\), while every other coordinate in \(C\) is multiplied by \(z_d(w)\).

## Q1. Pullback of the old ledger

Let \(u\) denote the divisor selected by `mergeIdx`, with exponent \(e=e_u\).

| Edge | Pullback of old diagonal coordinates | \(L(s)(B(w))\) |
|---|---|---|
| case-2 birth | Every old diagonal lies outside \(C\), hence is unchanged | \(L(s)(w)\) |
| case-1(1) merge | \(u=p=d\), so \(z_u(B(w))=z_u(w)\); all other old diagonals lie outside \(C\) | \(L(s)(w)\) |
| case-1(2) split | \(u\in C\setminus\{p,d\}\), so \(z_u(B(w))=z_d(w)z_u(w)\); other old diagonals are unchanged | \(\lvert z_d(w)\rvert^{e-1}L(s)(w)\) |
| rollover | No chart or state change | \(L(s)(w)\) |

In particular, in the split case,

\[
L(s)(B(w))
=
|z_d(w)z_u(w)|^{e-1}
\prod_{k\ne u}|z_{\operatorname{diag}_k}(w)|^{e_k-1}.
\]

## Q2. Edge identity

Set \(q=|C|-1\).

For a birth, the new divisor has exponent \(|C|\), hence ledger exponent \(q\):

\[
L(s')(w)=L(s)(w)|z_d(w)|^q.
\]

For a merge, \(d=u\) and \(e'_u=e+q\), so

\[
L(s')(w)
=L(s)(w)|z_u(w)|^q
=L(s)(B(w))|z_d(w)|^q.
\]

For a split, the old \(u\)-divisor remains unchanged, while the new \(d\)-divisor has

\[
e_d'=e+q.
\]

Therefore

\[
L(s')(w)
=L(s)(w)|z_d(w)|^{e+q-1}.
\]

On the other hand,

\[
\begin{aligned}
L(s)(B(w))\,|z_d(w)|^q
&=L(s)(w)|z_d(w)|^{e-1}|z_d(w)|^q\\
&=L(s)(w)|z_d(w)|^{e+q-1}.
\end{aligned}
\]

Thus the proposed identity holds for every edge:

\[
\boxed{
L(s)(B(w))\,|\det DB(w)|
=
L(s')(w).
}
\]

In case-1(2), the factor \(|z_d|^{e-1}\) comes from pulling back the old \(u\)-term:

\[
|z_u(B(w))|^{e-1}
=
|z_d(w)z_u(w)|^{e-1}.
\]

It does not come from the new divisor or directly from the chart determinant.

## Q3. Propagation of the invariant

Suppose

\[
|\det D\operatorname{acc}(x)|=L(s)(x)
\]

for every \(x\) in the relevant domain. For \(\operatorname{acc}'=\operatorname{acc}\circ B\), the chain rule gives

\[
\begin{aligned}
|\det D\operatorname{acc}'(w)|
&=|\det D\operatorname{acc}(B(w))|\,|\det DB(w)|\\
&=L(s)(B(w))\,|z_d(w)|^{|C|-1}\\
&=L(s')(w).
\end{aligned}
\]

The induction specifically needs:

- the hypothesis as a functional identity valid at \(B(w)\), not merely at the same symbol \(w\);
- the normalized-chart determinant formula;
- freshness, ensuring no unlisted old diagonal is modified;
- \(u\notin\{p,d\}\) in the split case;
- the composition order \(\operatorname{acc}'=\operatorname{acc}\circ B\).

At the root, \(\operatorname{acc}=\mathrm{id}\) and \(L=1\), so the invariant follows along every path. Rollover is immediate.

## Q4. Depth-3 mixed run

Choose distinct cells as follows:

\[
C_1=\{a,r,s,t\},\qquad p_1=r,\qquad d_1=a.
\]

The birth creates divisor \(A\) with \(e_A=4\):

\[
L_1=|z_a|^3.
\]

For the split, take the fresh block \(\{p,b\}\):

\[
C_2=\{a,p,b\},\qquad p_2=p,\qquad d_2=b.
\]

Here \(|C_2|-1=2\), so the new divisor \(B\) has

\[
e_B=e_A+2=6.
\]

Thus

\[
L_2=|z_a|^3|z_b|^5.
\]

For the merge into \(B\), take a fresh singleton \(\{q\}\):

\[
C_3=\{b,q\},\qquad p_3=d_3=b.
\]

This raises \(e_B\) from \(6\) to \(7\), giving

\[
L_3=|z_a|^3|z_b|^6.
\]

Let

\[
\Phi=B_1\circ B_2\circ B_3.
\]

The required coordinate relations are

\[
z_a(B_2(y))=z_b(y)z_a(y),
\qquad
z_a(B_3(w))=z_a(w),
\qquad
z_b(B_3(w))=z_b(w).
\]

Therefore

\[
\begin{aligned}
|\det D\Phi(w)|
&=
|z_a(B_2(B_3(w)))|^3
|z_b(B_3(w))|^2
|z_b(w)|\\
&=
|z_a(w)z_b(w)|^3|z_b(w)|^2|z_b(w)|\\
&=
\boxed{|z_a(w)|^3|z_b(w)|^6}
=
L_3(w).
\end{aligned}
\]

Hence the ledger invariant holds exactly for this mixed run.