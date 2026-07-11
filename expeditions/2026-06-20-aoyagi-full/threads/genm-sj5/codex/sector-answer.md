Bottom line: **NO**. A finite cover by the stated one-small-direction sectors cannot cover even almost all of the box near corank two. Letting \(\kappa\) vary makes the sector constant singular and produces a non-integrable overestimate. A joint multi-collapse estimate, or an analytically equivalent rank-stratified resolution, is required.

I use descending singular values \(s_1\ge s_2\ge s_3\), so \(s_3=\sigma_{\min}(P)\).

## Q1 — exact slice scaling

**DERIVED.** Suppose the \(k\) smallest singular values are comparable to \(\sigma\), while the other \(r-k\) are bounded above and below. Put

\[
d=m(r-k),\qquad e=mk,\qquad d+e=mr.
\]

Up to constants uniform in the spectral basis,

\[
g(P)\asymp
\int_{|x|,|y|\lesssim1}
\bigl(|x|^2+\sigma^2|y|^2\bigr)^{-c'}\,dx\,dy .
\]

For \(t=\sigma|y|\),

\[
\int_{|x|\le1}(|x|^2+t^2)^{-c'}dx
=
\omega_{d-1}t^{d-2c'}
\int_0^{1/t}\frac{z^{d-1}}{(1+z^2)^{c'}}\,dz .
\]

Consequently, assuming \(c'<mr/2\),

\[
g(P)\asymp
\begin{cases}
1, & 2c'<d,\\[2mm]
\log(1/\sigma), & 2c'=d,\\[2mm]
\sigma^{-(2c'-d)}, & d<2c'<mr.
\end{cases}
\]

Thus the power exponent is

\[
\boxed{\beta_k=\max\{0,\,2c'-m(r-k)\}},
\]

with a logarithmic correction when the maximum is attained at zero by equality.

For \(m=r=3\),

\[
\boxed{\beta_1=\max(0,2c'-6)},\qquad
\boxed{\beta_2=\max(0,2c'-3)}.
\]

In the relevant endpoint range \(3<c'<7/2\),

\[
\beta_1=2c'-6,\qquad \beta_2=2c'-3=\beta_1+3.
\]

For the explicit obstruction

\[
P_\sigma=[\operatorname{diag}(1,\sigma,\sigma)\ \ 0],
\]

one has

\[
g(P_\sigma)\asymp \sigma^{-(2c'-3)},
\]

whereas the codimension-one proposed majorant is only
\(\sigma^{-(2c'-6)}\). Their ratio is \(\sigma^{-3}\to\infty\).

**Verdict:** the codimension-one majorant is genuinely false on the two-collapse corner. At \(c'=3\), there is also a missed logarithm even on the one-collapse sector.

## Q2 — can one two-block sector cover close?

**NO — PROVEN by the corank-two family above.**

For finitely many fixed sectors with constants \(\kappa_i>0\), let
\(\kappa_*=\min_i\kappa_i\). Every such sector lies in

\[
\{s_2\ge\kappa_*\}.
\]

It therefore misses every \(P_\sigma\) with \(0<\sigma<\kappa_*\), an open positive-measure tube, not merely the exact rank-one locus.

Letting \(\kappa(P)=s_2(P)\) makes the predicate true, but destroys the estimate. The lower bound becomes

\[
\|A_0P\|^2
\ge s_3^2|v|^2+s_2^2|u|^2,
\qquad \dim u=6,\quad\dim v=3.
\]

For \(3<c'<7/2\),

\[
\int (s_3^2|v|^2+s_2^2|u|^2)^{-c'}\,du\,dv
\asymp
\boxed{s_2^{-6}s_3^{-(2c'-6)}}.
\]

The correct corank-two slice is instead

\[
\boxed{g(P)\asymp s_2^{-3}s_3^{-(2c'-6)}}.
\]

Thus the varying-\(\kappa\) bound loses an extra factor \(s_2^{-3}\). On the diagonal \(s_2=s_3=\sigma\), it gives \(\sigma^{-2c'}\) instead of the true
\(\sigma^{-(2c'-3)}\). Against a four-dimensional corank-two tube, the false majorant would require \(c'<2\), far short of \(7/2\).

**INFERENCE.** What is forced is an estimate retaining both collapsing scales and their joint measure. It may be implemented as a \(q\)-block estimate, sequential radial integrations, or a joint resolution, but it cannot be the original “one minimum versus uniformly stable remainder” estimate.

## Q3 — coupled \(7/2\) versus independent \(3/2\)

**PROVEN, conditional on \(U_0,U_1\) being uniformly positive units.**

Consider

\[
I(c')=\int
(u_0^2U_0+u_1^2U_1)^{-c'}
|u_0|^3|u_1|^2\,du_0du_1 .
\]

On the chart \(u_0=u,\ u_1=u\tau\), the Jacobian contributes \(|u|\), so

\[
|u_0|^3|u_1|^2\,du_0du_1
=
|u|^6|\tau|^2\,du\,d\tau,
\]

while the loss is \(u^2(U_0+\tau^2U_1)\). Hence the radial integral is

\[
\int_0^\varepsilon u^{6-2c'}\,du,
\]

which converges exactly when

\[
\boxed{c'<\frac72}.
\]

The complementary chart gives the same condition.

By contrast, replacing the additive corner by the multiplicative independent-divisor caricature

\[
(u_0u_1)^2U
\]

gives

\[
\int |u_0|^{3-2c'}|u_1|^{2-2c'}\,du_0du_1,
\]

whose threshold is

\[
\boxed{\min\left(\frac{4}{2},\frac{3}{2}\right)=\frac32}.
\]

So the verdict is exactly:

\[
\boxed{\text{coupled sum }=7/2,\qquad
\text{independent product split }=3/2.}
\]

The independent split creates false singularities along each coordinate axis.

Important caveat: if \(U_0\) or \(U_1\) can vanish, the \(7/2\) conclusion no longer applies; that degeneration must itself be assigned to a deeper rank cell.

There is also a measure caveat. The \(4+3\) model is correct for the intended deeper-product measure giving a four-dimensional corank-two tube. If \(P\) is literally a free \(3\times4\) matrix with Lebesgue \(dP\), the rank-\(\le1\) locus has codimension

\[
(3-1)(4-1)=6,
\]

so its corresponding corner would be \(6+3\), with candidate \(9/2\), not \(7/2\). Thus \(7/2\) presupposes that \(P\) is a deeper product/pushforward, not an independently Lebesgue-distributed matrix.

## Q4 — measurability

**YES — PROVEN.** Let \(\ell=r-q\), and define

\[
M_\ell(P)=\max_{|I|=|J|=\ell}|\det P_{I,J}|.
\]

This is a finite maximum of absolute values of polynomials, hence continuous and Borel measurable. Cauchy–Binet gives

\[
\sum_{I,J}(\det P_{I,J})^2
=
e_\ell(PP^\top)
=
\sum_{i_1<\cdots<i_\ell}s_{i_1}^2\cdots s_{i_\ell}^2.
\]

If \(N=\binom r\ell\binom n\ell\), then

\[
\frac{s_1\cdots s_\ell}{\sqrt N}
\le M_\ell(P)
\le s_1\cdots s_\ell.
\]

On a bounded box, \(s_1\le R\), so minor bands and \(s_\ell\)-bands sandwich one another up to constants:

\[
\{s_\ell\ge\kappa\}
\subseteq
\{M_\ell\ge\kappa^\ell/\sqrt N\},
\]

\[
\{M_\ell\ge\kappa'\}
\subseteq
\{s_\ell\ge\kappa'/R^{\ell-1}\}.
\]

These are quantitatively equivalent, though not literally the same threshold set.

Exact rank cells are semialgebraic:

\[
\{\operatorname{rank}P=\ell\}
=
\{M_\ell>0\}\cap\{M_{\ell+1}=0\}.
\]

Therefore there is **no measurability obstruction** to a finite rank-stratified cover. The obstruction is analytic: the lower-rank cells require different coupled estimates. Measurable minor cells do not rescue the single-sector proof.