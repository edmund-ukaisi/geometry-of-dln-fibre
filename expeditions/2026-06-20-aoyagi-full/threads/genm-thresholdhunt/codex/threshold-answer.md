Let
\[
m=M_0,\qquad n=M_1,\qquad p=M_2.
\]
Because \(W=[z_0;A_{\rm cor}]\) fills all \(n\) rows, \(u\) does not affect the true threshold.

## 1. Exact threshold

### Facts: codimension

Stratify
\[
Z=\{(B,W):BW=0\}
\]
by \(r=\operatorname{rank}B\), where \(0\le r\le q:=\min(m,n)\).

The rank-\(r\) matrices \(B\) form a manifold of dimension
\[
r(m+n-r).
\]
For fixed \(B\), every column of \(W\) must lie in the \((n-r)\)-dimensional kernel of \(B\), contributing \(p(n-r)\) parameters. Hence
\[
\operatorname{codim} Z_r
=mn+np-r(m+n-r)-p(n-r)
=(m-r)(n-r)+rp.
\]
Therefore
\[
C:=\operatorname{codim}Z
=\min_{0\le r\le q}\bigl((m-r)(n-r)+rp\bigr).
\]

Writing \(d=|m-n|\), this minimum is
\[
C=
\begin{cases}
p\min(m,n),&p\le d,\\[2mm]
mn-\left\lfloor\dfrac{(m+n-p)^2}{4}\right\rfloor,
   &d<p<m+n,\\[3mm]
mn,&p\ge m+n.
\end{cases}
\]
The adjacent formulas agree at the boundary points.

### Inference: RLCT equals \(C/2\)

The codimension argument alone gives \(\lambda^*\le C/2\). Here equality holds.

Indeed, use a positive Gaussian localization and set
\[
J(t)=\int e^{-\|B\|^2-\|W\|^2-t\|BW\|^2}\,dB\,dW.
\]
Integrating over \(W\) gives, up to harmless constants,
\[
J(t)=\int e^{-\|B\|^2}
\det(I+tB^{\mathsf T}B)^{-p/2}\,dB.
\]
Let \(x_1,\dots,x_q\) be the nonzero squared singular values of \(B\). Their real-Wishart density contains
\[
\prod_i x_i^{(d-1)/2}\prod_{i<j}|x_i-x_j|.
\]
The ordered-eigenvalue blow-up gives one candidate exponent for each number \(k\) of singular values of size \(t^{-1}\):
\[
\lambda_k
=\frac{k(d+1)+k(k-1)+p(q-k)}2
=\frac{k(d+k)+p(q-k)}2.
\]
Putting \(r=q-k\),
\[
2\lambda_k=(m-r)(n-r)+rp.
\]
Thus no singular stratum produces an exponent below \(C/2\), while a smooth point of a maximal-dimensional component realizes \(C/2\). Consequently
\[
\boxed{\lambda^*=\frac12
\min_{0\le r\le\min(M_0,M_1)}
\left((M_0-r)(M_1-r)+rM_2\right)}.
\]

Hence
\[
\boxed{I(c)<\infty\iff 0<c<\lambda^*.}
\]
At \(c=\lambda^*\), the integral diverges.

## 2–3. Concrete cases and claimed value

| Case | \(\operatorname{codim}\{BW=0\}\) | \(\lambda^*\) | \(\lambda_{\rm claim}\) | Comparison |
|---|---:|---:|---:|---|
| A: \((3,3,3,2)\) | \(7\) | \(7/2=3.5\) | \(7/2=3.5\) | EQUAL |
| B: \((4,4,4,3)\) | \(12\) | \(6\) | \(13/2=6.5\) | ABOVE |
| C: \((6,6,6,4)\) | \(27\) | \(27/2=13.5\) | \(14\) | ABOVE |

- **A:** Sound and sharp.
- **B:** Overclaims convergence; for example \(c=6.25<6.5\) already diverges.
- **C:** Overclaims convergence; for example \(c=13.75<14\) already diverges.