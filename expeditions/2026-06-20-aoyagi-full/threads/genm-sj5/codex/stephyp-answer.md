Let \(\lambda(F)\) denote the critical exponent for local integrability of \(F^{-c}\).

### Q1 — SOUND [DERIVED]

Before the corner blow-up, the loss is
\[
G=u_0^2U_0+u_1^2U_1.
\]
On the sector \(|u_1|\le |u_0|\), write \(u_1=u_0\tau\), \(|\tau|\le1\). Since
\[
du_0\,du_1=|u_0|\,du_0\,d\tau,
\]
the integrand becomes
\[
|u_0|^{p_0+p_1+1-2c}|\tau|^{p_1}
  (U_0+\tau^2U_1)^{-c}\,du_0\,d\tau.
\]
If
\[
0<a\le U_0+\tau^2U_1\le b<\infty,
\]
then the unit factor is harmless, and for \(p_i>-1\),
\[
\int_0^\varepsilon u_0^{p_0+p_1+1-2c}\,du_0<\infty
\iff
c<\frac{p_0+p_1+2}{2}.
\]
Thus
\[
\boxed{\lambda(G)=\frac12\bigl((p_0+1)+(p_1+1)\bigr)}.
\]
At equality the \(u_0\)-integral is logarithmically divergent. The reciprocal chart \(u_0=u_1\sigma\) is required for the other sector.

The factor \(u_0^2\) here is an exceptional factor representing the simultaneous collapse of both original radii. The deeper block contributes through both
\[
|u_1|^{p_1}=|u_0|^{p_1}|\tau|^{p_1}
\quad\text{and}\quad
du_1=|u_0|\,d\tau.
\]
That is where its full charge \(p_1+1\) enters.

By contrast,
\[
F=z^2(x^2+y^2)
\]
has
\[
\int F^{-c}\,dxdydz
=
\left(\int |z|^{-2c}dz\right)
\left(\int_0^\varepsilon r^{1-2c}dr\right)d\theta.
\]
The conditions are \(c<1/2\) and \(c<1\), hence
\[
\boxed{\lambda\bigl(z^2(x^2+y^2)\bigr)=\min(1/2,1)=1/2}.
\]

The collapse comes from the genuine pre-existing divisor \(z=0\): \(x,y\) remain independent when \(z=0\). Algebraically, \((zx,zy)=z(x,y)\) has a common factor. The coupled sum has zero set \(u_0=u_1=0\), not the union of two independent zero divisors.

Therefore the sum-form is immune exactly when its residual bracket is a unit on the relevant chart. If the \(\tau\)-box contains \(0\), then
\[
(U_0+\tau^2U_1)|_{\tau=0}=U_0,
\]
so uniform invertibility of the bracket requires uniform invertibility of \(U_0\) there. A lower bound proves the needed finiteness; the usual compact-chart upper bound gives the exact equality above.

### Q2 — NEEDS-SECTOR [DERIVED]

Pointwise full rank is not a uniform unit estimate.

For example,
\[
A_2(t)=\operatorname{diag}(1,\ldots,1,t),\qquad 0<t\le1,
\]
is full rank for every \(t>0\), but
\[
\sigma_{\min}(A_2(t))=t,\qquad
\det(A_2A_2^\top)=t^2\longrightarrow0.
\]
The same occurs for a squared pivot minor. Thus the open full-rank locus accumulates on the rank-drop locus, and
\[
U_0(A_2)>0\ \text{pointwise}
\quad\not\Rightarrow\quad
\inf U_0>0.
\]

Pointwise nonvanishing is enough near one fixed full-rank matrix after shrinking its neighborhood. It is not enough for a single chart whose closure meets rank drop. One needs a quantitative sector such as
\[
\sigma_{\min}(A_2)\ge\varepsilon,
\]
together with the appropriate pivot-minor sector if \(U_0\) is one particular minor rather than the full Gram determinant.

Hence the exact rank-drop locus cannot merely be deleted as measure zero. Its entire neighborhood, where \(U_0\) is small and the constants blow up, must be assigned to another branch.

### Q3 — SOUND for the stated anchor; GAP for a bare “recurse” assertion

[DERIVED] A deeper branch can genuinely have a lower threshold. Suppose near rank drop that \(z\in\mathbb R^D\),
\[
U_0\asymp |z|^{2m},\qquad U_1\asymp1.
\]
Put \(n_i=p_i+1\). The local model
\[
F=u_0^2|z|^{2m}+u_1^2
\]
has
\[
\boxed{\lambda(F)=\frac{n_1}{2}
+\frac12\min\!\left(n_0,\frac{D}{m}\right)}.
\]
Thus the full coupled value \((n_0+n_1)/2\) is recovered only if
\[
D/m\ge n_0.
\]
Codimension alone is not enough: the vanishing order \(m\) matters. Similarly, if both units share a factor,
\[
U_0,U_1\asymp |z|^{2m},
\]
then
\[
\lambda=\min\!\left(\frac{D}{2m},\frac{n_0+n_1}{2}\right),
\]
which is exactly the product-collapse mechanism.

The cited warning model confirms this:
\[
x^2(x^2+y^{2N})=x^4+x^2y^{2N}
\]
has
\[
\lambda=\frac{N+1}{4N}<\frac12\qquad(N>1).
\]

[INFERRED from the established joint density] For the anchor \((3,3,3,4)\), however, the required deeper-branch estimate is already precisely the stated joint one:
\[
\int s_2^{-3}s_3^{-\eta}\,d\mu<\infty
\iff \eta<1.
\]
Since \(\eta=2c'-6\),
\[
2c'-6<1\iff c'<\frac72.
\]
Therefore this rank-drop tube does not undershoot \( \frac12\minAdm=7/2\). The joint estimate—not genericity, null-set deletion, or marginal bounds—is what secures it.

The split must establish:

- uniform coercivity and bounded chart Jacobians on the quantitative full-rank sector;
- a joint tube estimate on the whole small-singular-value neighborhood;
- every recursive branch has threshold at least \(\frac12\minAdm\), accounting for both tube density and vanishing orders;
- uniform seam control and termination of the rank stratification.

Final diagnosis: there is no collapse intrinsic to the uniformly coercive coupled sum. There is a genuine collapse mechanism at a vanishing-unit boundary, but the stated anchor’s joint density neutralizes it. Thus the estimate is sound given quantitative sectors plus the proved joint recursive bound; “full rank generically, so recurse” alone is a gap.

The cheapest collapse check is to compute, on the first rank-drop normal chart, the tube exponent \(D-1\) and the leading order \(U_0\asymp\rho^{2m}\). If
\[
\frac{n_1}{2}+\frac12\min(n_0,D/m)
<\frac{n_0+n_1}{2},
\]
a hidden collapse has been exposed. A one-dimensional path \(U_0\to0\) without its tube measure is not decisive.