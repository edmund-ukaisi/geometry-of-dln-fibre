## 1. THE CODIM-WITH-CHARGE

Put \(s=\rho-k\). On a compact \(P,B,C\)-chart, the change
\[
W=z_0+P^{-1}BA_{\rm cor}
\]
has unit Jacobian and
\[
E_{\rm top}+E_{\rm tr}\asymp \|WZ\|_F^2.
\]

For comparable lost singular values,
\[
Z_t\simeq \operatorname{diag}(I_s,tI_k),
\]
write \(W=(W_0,W_1)\) and \(A_{\rm cor}=(X,Y)\). Then
\[
\|WZ_t\|^2\asymp |W_0|^2+t^2|W_1|^2,
\]
with \(\dim W_0=us\), \(\dim W_1=uk\), while
\[
\det(Q_bQ_b^\top)\asymp
\det(XX^\top+t^2YY^\top).
\]

The stated charge \(t^{-a(b-s)_+}\) is only the generic-\(A_{\rm cor}\) exponent. Since \(A_{\rm cor}\) is integrated, one must also resolve the strata \(\operatorname{rank}X=b-h\), where
\[
(b-s)_+\le h\le b.
\]
Their normal codimension is
\[
c_h=h(s-b+h),
\]
and the charge contributes \(t^{-ah}\). Hence integration in \(A_{\rm cor}\) produces the exact worst exponent
\[
\gamma_s
 =\max_{(b-s)_+\le h\le b}
 \bigl(ah-c_h\bigr)
 =\max_{(b-s)_+\le h\le b}h(a+b-s-h).
\]
The generic-\(A_{\rm cor}\) model corresponds only to \(h=(b-s)_+\), giving \(a(k-d)_+\).

Thus the remaining radial model is
\[
\int t^{\kappa_k-1-\gamma_s}
 \bigl(|y|^2+t^2|w|^2\bigr)^{-q}\,dt\,dy\,dw .
\]
Integrating \(y\), then using \(R=|w|\), gives
\[
2q<us+\kappa_k-\gamma_s,\qquad
2q<u(s+k)=u\rho.
\]
Therefore
\[
\boxed{
C_k=
\min\!\left\{
u\rho,\;
u(\rho-k)+\kappa_k-\gamma_{\rho-k}
\right\}.}
\]

The rank slack ensures the charge itself is integrable: from the CR recursion,
\[
\kappa_k\ge \binom{k+1}{2},
\qquad
\gamma_s\le
\left\lfloor\frac{(a+b-s)^2}{4}\right\rfloor
\le
\left\lfloor\frac{(k-1)^2}{4}\right\rfloor
<\kappa_k.
\]

At full collapse \(s=0\), necessarily \(h=b\), so \(\gamma_0=ab\). Hence
\[
\boxed{
C_{\rm full}
=\min\!\left\{
u\rho,\;
\minAdm(M_2,\ldots,M_{\rm last})-ab
\right\}.}
\]

This is exact for the standard rank-stratified normal model. Facts (i)–(ii) alone do not prove that arbitrary hierarchical composite-product degenerations admit only these charts; a formal proof still needs the corresponding stratified-resolution or induction lemma.

## 2. VERDICT: BOUNDED

There is no numerical wall. For every \(s=\rho-k\),
\[
\boxed{
C_k\ge \minAdm(M)-ab.}
\]

Indeed, let \(h\) attain \(\gamma_s\). Then
\[
ab+us-\gamma_s
=us+(a-h)(b-h)+hs=:R_h.
\]
The three-chain front QIP satisfies
\[
\minAdm(M_0,M_1,s)\le R_h:
\]

- if \(h\le a\), \(R_h\) is exactly its value at the admissible cut \(u+h\);
- if \(h>a\), then \(M_0<M_1\) and
  \[
  R_h-M_0s=(h-a)(s-b+h)\ge0,
  \]
  so the endpoint cut gives the bound.

Stratifying by the rank \(s\) of the deep product gives
\[
\minAdm(M)
\le
\kappa_k+\minAdm(M_0,M_1,s)
\le
\kappa_k+ab+us-\gamma_s.
\]
After subtracting \(ab\), this is precisely the required deep branch inequality. Taking \(s=\rho\) also gives
\[
\minAdm(M)-ab\le u\rho.
\]

Thus the already-known generic-\(Z\) front resolution is binding; deep rank drops may tie it but cannot undercut it.

At full collapse the decisive comparison is
\[
\boxed{
\minAdm(M_2,\ldots,M_{\rm last})
\ \ge\
\minAdm(M).}
\]
It cannot fail: forcing the deep product to vanish already forces the whole product to vanish, so the full zero-product locus has no larger codimension.

The combinatorial inequality is width-unconditional. The first analytic wall from growing the front defects occurs when
\[
a>\rho-b
\quad\Longleftrightarrow\quad
a+b\ge\rho+1,
\]
where the determinant charge is already non-integrable for generic full-rank \(Z\). The strict-shell hypothesis lies safely inside this wall.

## 3. RATIO VERSUS INTEGRAL

The factor \(r^{-ab}\) proves only that uniform domination by the bare comparator fails.

At full collapse the relevant radial integral is instead
\[
\int_0^\varepsilon
r^{\,\kappa_\rho-1-ab-2q}\,dr,
\]
which converges when
\[
2q<\kappa_\rho-ab.
\]
Since \(\kappa_\rho=\minAdm(\text{deep})\ge\minAdm(M)\), this holds for every \(2q<\minAdm(M)-ab\).

So the ratio blow-up does not imply divergence of the integral; it kills only the bare-comparator domination route.