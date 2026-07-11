## Q1 — common-corner blow-up

**FACT.** On the chart
\[
u_0=u,\qquad u_1=u\tau,
\]
the generators transform as
\[
u_0\mapsto u,\qquad u_1\mapsto u\tau.
\]
Thus, with columns ordered \((u,\tau)\),
\[
e'=\begin{pmatrix}1&0\\1&1\end{pmatrix},
\qquad
\operatorname{sharedDivisorExp}(e')=(1,0).
\]

The first row realizes both minima, so this chart is dehomogenised. Moreover,
\[
G(u,u\tau)=u^2\bigl(U_0(u,u\tau)+\tau^2U_1(u,u\tau)\bigr),
\]
whose parenthesized factor is a unit whenever \(U_0\ge a>0\).

The change-of-variables determinant is
\[
\left|\det\frac{\partial(u_0,u_1)}{\partial(u,\tau)}\right|=|u|.
\]
Hence
\[
|u_0|^{h_0}|u_1|^{h_1}\,du_0du_1
=
|u|^{h_0+h_1+1}|\tau|^{h_1}\,du\,d\tau.
\]
Therefore
\[
(h_u,h_\tau)=(h_0+h_1+1,h_1).
\]
For \((p_0,p_1)=(4,3)\), so \((h_0,h_1)=(3,2)\),
\[
(h_u,h_\tau)=(6,2).
\]
Only the \(u\)-column has positive shared exponent, so
\[
\operatorname{monomialThreshold}
=\frac{h_u+1}{2}
=\frac{6+1}{2}
=\frac72.
\]

The complementary chart \(u_1=u,\ u_0=u\tau\) has support
\[
\begin{pmatrix}1&1\\1&0\end{pmatrix}
\]
and gives the same threshold. Both charts are needed to cover the corner.

For \(m\) blocks, on the chart with pivot \(r\),
\[
u_r=\rho,\qquad u_k=\rho\tau_k\quad(k\ne r),
\]
we obtain
\[
e'_{i,\rho}=1,\qquad e'_{i,\tau_k}=\mathbf 1_{i=k},
\]
so
\[
\operatorname{sharedDivisorExp}(e')=(1,0,\ldots,0).
\]
The pivot row realizes all minima. Since the Jacobian is \(|\rho|^{m-1}\),
\[
H_\rho=\sum_k h_k+(m-1)
      =\sum_k(p_k-1)+(m-1)
      =\sum_kp_k-1.
\]
Consequently,
\[
\frac{H_\rho+1}{2}
=\frac12\sum_kp_k.
\]

**INFERENCE.** The support/terminal algebra gives the desired sum exactly after a finite \(m\)-chart common-corner blow-up.

## Q2 — what `radialAttach` represents

**FACT.** Repeated `radialAttach` gives every generator exponent \(1\) in every new coordinate:
\[
e(i,k)=1.
\]
Hence
\[
G_{\rm radial}
=\left(\prod_k u_k^2\right)U,
\]
and its weighted integrand separates:
\[
G_{\rm radial}^{-c'}\prod_k|u_k|^{h_k}
\asymp
\prod_k|u_k|^{h_k-2c'}.
\]
It is finite precisely when
\[
h_k-2c'>-1\quad\forall k,
\]
that is,
\[
c'<\frac12\min_k(h_k+1)
   =\frac12\min_kp_k.
\]
For \(p=(4,3)\), this is \(3/2\), not \(7/2\).

The block-diagonal support is instead built using
\[
a_k(i)=\mathbf 1_{\{\beta(i)=k\}}
\]
in `prependColumn`, where \(\beta(i)\) is the block containing generator \(i\). Then
\[
e(i,k)=\mathbf 1_{\{\beta(i)=k\}},
\qquad
G=\sum_k u_k^2U_k.
\]

**INFERENCE.** `radialAttach` models the multiplicative product/minimum mechanism. Indicator-column prepending models the additive block support.

## Q3 — carrier fit

**FACT.** `radialAttach_integral` is not the required toric transport: it proves
\[
(D.\mathrm{radialAttach}\ h).I(c')
=
I_{\rm radial}(h,c')\,D.I(c'),
\]
using the pointwise product \(u^2D.\mathrm{loss}\). It does not implement \(u_k=\rho\tau_k\), its Jacobian, or the finite pivot-chart cover.

The exact weighted two-block endpoint is already banked as [`sjSlice_corner_two_block_lt_top`](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJSlice334.lean:77). It proves
\[
\int
(u_0^2U_0+u_1^2U_1)^{-c'}
|u_0|^{h_0}|u_1|^{h_1}<\infty
\]
for
\[
c'<\frac{h_0+h_1+2}{2},
\]
assuming \(U_0,U_1\ge a>0\). Thus the concrete \(7/2\) corner is already closed.

The flat theorem also matches the general weighted corner exactly. Put
\[
P=\sum_kp_k,\qquad p_k=h_k+1.
\]
For \(U_k\ge a>0\),
\[
G(u)\ge a\sum_ku_k^2.
\]
Writing \(x_k\in\mathbb R^{p_k}\) and \(u_k=\|x_k\|\), blockwise polar coordinates give
\[
\int_{\prod_kB^{p_k}}
F(\|x_1\|,\ldots,\|x_m\|)\,dx
=
C_p\int_{[0,1]^m}F(u)\prod_ku_k^{p_k-1}\,du,
\]
with \(0<C_p<\infty\). Taking \(F(u)=(\sum u_k^2)^{-c'}\), the left side is a restriction of the \(P\)-dimensional flat isotropic corner. Therefore [`corner_block_cube_lintegral_lt_top`](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJRadialPolar.lean:257) gives finiteness for
\[
c'<P/2=\frac12\sum_k(h_k+1).
\]

Equivalently, weighted AM–GM with \(w_k=p_k/P\) gives
\[
G^{-c'}\prod_k|u_k|^{p_k-1}
\le
a^{-c'}\prod_k|u_k|^{\,p_k-1-2c'p_k/P},
\]
and every exponent exceeds \(-1\) exactly when \(c'<P/2\).

**INFERENCE — decisive verdict.** **FITS.** The banked assembly is:

\[
\text{indicator `prependColumn`}
\;\longrightarrow\;
\text{block-additive carrier}
\;\longrightarrow\;
\text{uniform unit lower comparison}
\;\longrightarrow\;
\text{weighted two-block/joint flat-corner endpoint}.
\]

No new carrier constructor is required. A convenience multi-block wrapper could be added, but it would package existing semantics rather than introduce a new operation.

The uniform units-bounded-below hypothesis is required on each good sector. The rank-drop complement, where that bound fails, must be routed through separate charts/strata; `radialAttach` cannot absorb it.