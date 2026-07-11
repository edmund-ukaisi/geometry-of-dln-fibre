Assume \(1\le b\le m<q\). Then the exact answer is

\[
\boxed{I(a)<\infty \iff 0<a<m-b+1.}
\]

Thus

\[
\boxed{a_c(b,m,q)=m-b+1.}
\]

At \(a=a_c\) the divergence is logarithmic. There is no seam/Beta divergence below \(a_c\).

## Q1 — Dominant-minor seams

**Status: PROVED. No boundary or seam term is created.**

Let \(\Delta_S(A)=\det A_S\). Choose a measurable tie-breaking rule and partition the full-row-rank locus into

\[
E_S=\{A:|\Delta_S|\ge |\Delta_T|\ \forall T,\text{ with ties assigned by order}\}.
\]

This is multiplication by characteristic functions, not integration by parts. Hence there is no boundary flux or surface term.

For \(S\ne T\), the seam is contained in

\[
\Delta_S(A)^2-\Delta_T(A)^2=0,
\]

the zero set of a nonzero polynomial, hence an ambient Lebesgue-null set. Assigning it to either chart does not change the integral.

At a point where both minors are nonzero, the transition is

\[
Q_T=Q_S\,A_S^{-1}A_T,
\qquad
\left|\det(A_S^{-1}A_T)\right|
 =\frac{|\Delta_T|}{|\Delta_S|}.
\]

On the seam this determinant equals \(1\), so the rowwise transition Jacobian equals \(1^b=1\). There is no Beta factor.

The integrand is singular exactly when

\[
\operatorname{rank}(YA)<b.
\]

If \(A\) has full row rank \(m\), then \(\operatorname{rank}(YA)=\operatorname{rank}Y\). Thus a nonzero seam is not itself singular. At any seam point with \(\operatorname{rank}(YA)=b\), the integrand is continuous and locally bounded. It can still be singular on the intersection with \(\{\operatorname{rank}Y<b\}\), but that singularity has nothing to do with chart switching.

A correction to the rank language: two maximal minors vanishing does not imply \(\operatorname{rank}A\le m-2\). All maximal minors vanish iff \(\operatorname{rank}A\le m-1\).

## Q2 — What cancels, and what can go wrong in a bound?

**Status: DERIVED EXACTLY. The moving domain cancels the naked Jacobian, but not every intrinsic scaling singularity.**

Put \(r=q-m\), reorder columns so \(S\) comes first, and write

\[
A=(M,C)=M[I_m\ B],\qquad M=A_S,\qquad B=M^{-1}C.
\]

Dominance implies every entry of \(B\) is bounded by \(1\), by Cramer’s rule. The exact Jacobians are

\[
dA=|\det M|^r\,dM\,dB,
\qquad
X=YM,\quad dY=|\det M|^{-b}\,dX.
\]

Therefore the exact chart integral has the form

\[
\int |\det M|^{r-b}
  \int_{D_M}
  \det\!\bigl(X(I+BB^T)X^T\bigr)^{-a/2}\,dX\,dM\,dB,
\]

where

\[
D_M=[-1,1]^{b\times m}M,
\qquad
\operatorname{vol}(D_M)=2^{bm}|\det M|^b.
\]

For a bounded integrand, that volume cancels the entire \(|\det M|^{-b}\). At \(a=0\), for example, the resulting power is \(|\det M|^r\), not \(|\det M|^{r-b}\).

For \(a>0\), an intrinsic residual dependence on \(M\) can remain because \(Q\) itself becomes small. In \((b,m,q)=(1,1,2)\), on the chart

\[
A=(s,st),\qquad |t|\le1,
\]

one obtains

\[
|s|^{-1}\int_{-|s|}^{|s|}|x|^{-a}(1+t^2)^{-a/2}\,dx
 =C_a|s|^{-a}(1+t^2)^{-a/2}.
\]

The \(|s|^{-1}\) Jacobian is cancelled; the remaining \(|s|^{-a}\) is the genuine scaling of \(Q\), not a seam pole.

### A real wall for a crude per-chart bound

If one replaces \(D_M\) by a fixed box, the remaining outer majorant contains

\[
\int |\det M|^{r-b}\,dM.
\]

This diverges whenever \(r<b\), since \(r-b\le-1\) and near a generic rank-\((m-1)\) matrix, \(\det M\) is a smooth transverse coordinate.

Thus:

- \((2,3,4)\): \(r-b=1-2=-1\), giving a false logarithmic \(\int dt/|t|\).
- \((2,2,3)\): again \(r-b=-1\).
- This false bound diverges even at \(a=0\).

It is a divergence of the bound, not of the exact chart integral. It occurs already with \(B\) strictly inside the dominant chart; it is not caused by the seam.

As \(M\to\) singular while remaining dominant, all maximal minors tend to zero, so the limit lies in \(\{\operatorname{rank}A\le m-1\}\). Deeper rank drops create no subcritical divergence: conditioning on full-rank \(Y\), the entire \(A\)-integration has threshold \(q-b+1\), and

\[
m-b+1<q-b+1.
\]

Hence all \(A\)-rank strata have slack throughout \(a<a_c\).

## Q3 — Exact threshold and clean proof

**Status: PROVED.**

Let \(Y,A\) instead have independent standard Gaussian entries. Conditional on \(Y\), the \(q\) columns of \(YA\) are independent \(N(0,YY^T)\) vectors. Hence

\[
\mathbb E_A\!\left[\det(YAA^TY^T)^{-a/2}\mid Y\right]
 =M_{b,q}(a)\det(YY^T)^{-a/2},
\]

where the Wishart negative moment is

\[
M_{b,n}(a)
 =2^{-ab/2}\frac{\Gamma_b((n-a)/2)}{\Gamma_b(n/2)}
\]

and is finite exactly when

\[
a<n-b+1.
\]

Applying this again to \(Y\),

\[
\mathbb E\det(YAA^TY^T)^{-a/2}
 =M_{b,q}(a)M_{b,m}(a).
\]

Because \(m<q\), this is finite exactly for

\[
a<m-b+1.
\]

The Gaussian density is bounded below on the box, so Gaussian finiteness implies box finiteness.

For sharp divergence, take \(A\) in a neighborhood of

\[
A_0=c[I_m\ 0],\qquad 0<c<1.
\]

Then \(AA^T\) is uniformly comparable to \(I_m\). Near a rank-\((b-1)\) matrix \(Y\), write the last row as tangential coordinates plus

\[
z\in\mathbb R^{m-b+1}
\]

normal to the span of the first \(b-1\) rows. The Schur-complement identity gives

\[
\det(YY^T)
 =\det(RR^T)\,\|z\|^2.
\]

Thus the normal integral is

\[
\int_0^\varepsilon r^{m-b-a}\,dr,
\]

finite exactly when \(a<m-b+1\), and logarithmically divergent at equality.

The requested values are:

| \((b,m,q)\) | \(a_c\) |
|---|---:|
| \((2,3,4)\) | \(2\) |
| \((1,3,4)\) | \(3\) |
| \((1,1,2)\) | \(1\) |
| \((2,2,3)\) | \(1\) |
| \((1,2,3)\) | \(2\) |

Examples:

\[
(1,1,2):\quad \det(QQ^T)=y^2(a_1^2+a_2^2),
\]

so the thresholds are \(1\) from \(y\) and \(2\) from \(A\), giving \(a_c=1\).

For \((2,2,3)\),

\[
\det(QQ^T)=\det(Y)^2\det(AA^T),
\]

and the \(|\det Y|^{-a}\) factor has threshold \(1\).

A single squared \(b\times b\) Cauchy–Binet minor is generally lossy: its inverse moment has threshold only \(a<1\). A fixed block of \(m\) columns is sharp:

\[
QQ^T\succeq Q_SQ_S^T,\qquad |S|=m,
\]

and the corresponding two-Wishart calculation gives \(a<m-b+1\).

**The clean proof does not need the dominant-minor cover or its seams.**

## Q4 — Steelmanned wall

**Status: NO genuine subcritical wall. YES at the endpoint; YES for a lossy bound.**

For every \(a<a_c\), the whole nonnegative integral is finite. Consequently every measurable chart subintegral is finite. Since the chart change of variables is an exact bijection on the full-rank locus, it cannot manufacture a genuine divergence.

The genuine wall is

\[
a=a_c=m-b+1.
\]

It is the logarithmic normal integral

\[
\int_0^\varepsilon \frac{dr}{r},
\]

coming from \(Y\) dropping rank by one while \(A\) remains uniformly full row rank and can lie strictly inside a unique dominant chart. It is therefore neither a seam nor a deep-\(A\)-rank phenomenon.

The strongest false wall is the fixed-image per-chart bound for \((2,3,4)\) or \((2,2,3)\):

\[
\int |\det A_S|^{-1}\,dA_S=\infty.
\]

That divergence is real for the bound, even at \(a=0\), but disappears when the shrinking image \(D_{A_S}\) is retained.

Final verdict:

- Beta/seam divergence in \(I(a)\): **NO**.
- Residual determinant divergence in a crude chart majorant: **YES**.
- True finiteness: **exactly \(a<m-b+1\)**.
- Endpoint \(a=a_c\): **true logarithmic divergence**.
- Dominant-minor cover needed for the clean proof: **NO**.