I take the intended range to be \(3<c'<7/2\). Two corrections: at \(c'=3\) logarithms replace the claimed power, and the setup’s \(q\) is not corank—it satisfies \(q-1=\) limiting rank.

For \(k\) small singular values \(\asymp\sigma\), with the others bounded below, put \(d_k=3(3-k)\). Radial scaling gives
\[
g(P)\asymp
\begin{cases}
1,&2c'<d_k,\\
\log(1/\sigma),&2c'=d_k,\\
\sigma^{-(2c'-d_k)},&2c'>d_k.
\end{cases}
\]

## Q1

For \(s_1\asymp1\) and \(s_2=s_3=\sigma\), \(d_2=3\), hence
\[
g(P)\asymp \sigma^{-\beta_2},
\qquad \beta_2=2c'-3.
\]
Meanwhile the proposed majorant is
\[
\sigma_{\min}^{-\alpha'}=\sigma^{-(2c'-6)}.
\]
Their ratio grows as \(\sigma^{-3}\). Therefore no uniform constant can make the proposed bound global.

It is valid only sectorially, for \(s_2\ge\kappa>0\), with a constant depending on \(\kappa\). Strictly, \(s_1=O(1)\) is insufficient for the displayed asymptotic; one needs \(s_1\asymp1\).

**FACT vs INFERENCE:** FACT—\(\beta_2=2c'-3=\alpha'+3\). INFERENCE—the step-(a) bound is sectorial, not global.

## Q2

The shell measure of a codimension-\(D_k\) tube is \(\sigma^{D_k-1}\,d\sigma\), so convergence requires \(\beta_k<D_k\).

| \(k\) | \(\beta_k\) near \(c'=7/2\) | \(D_k\) | Convergence |
|---:|---:|---:|---:|
| 1 | \(2c'-6\) | 1 | \(c'<7/2\) |
| 2 | \(2c'-3\) | 4 | \(c'<7/2\) |
| 3 | \(2c'\) | 8 | \(c'<4\) |

At \(c'=7/2\), both \(k=1\) and \(k=2\) give the borderline integral \(\int_0^\varepsilon \sigma^{-1}\,d\sigma\). Thus both strata are binding at the same threshold. The all-small stratum binds only at \(c'=4\).

**FACT vs INFERENCE:** FACT—\((D_k+\!d_k)/2=(7/2,7/2,4)\). INFERENCE—\(k=1\) is not the sole obstruction; \(k=2\) is equally binding.

## Q3

On the two-small-singular-value stratum,
\[
g(P)\asymp \sigma^{-(2c'-3)}.
\]

For \(W=\sigma_{\min}^{-a}\),
\[
W\asymp\sigma^{-a},
\qquad a\ge 2c'-3.
\]
Near \(c'=7/2\), this forces \(a\approx4\), not \(a<1\).

For \(W=\det(G)^{-a/2}\), since
\[
\det(G)=s_1^2s_2^2s_3^2\asymp\sigma^4,
\]
we have
\[
W\asymp\sigma^{-2a},
\qquad 2a\ge2c'-3,
\qquad a\ge c'-\frac32.
\]
Near \(c'=7/2\), this forces \(a\approx2\), again not \(a<1\).

Thus no single global majorant of either Layer-2-integrable form exists in the intended range.

**FACT vs INFERENCE:** FACT—the forced exponents are \(2c'-3\) and \(c'-3/2\). INFERENCE—the codimension-four stratum rules out both restricted global majorants.

## Q4

Route (a) is essentially right but needs a guard: its displayed inequality alone incorrectly includes \(G=0\).

Let \(t=\kappa^2\), with eigenvalues \(\lambda_1\ge\lambda_2\ge\lambda_3\ge0\). Then
\[
\|G\|_{\mathrm{op}}=\lambda_1,\qquad
\|\wedge^2G\|_{\mathrm{op}}=\lambda_1\lambda_2.
\]
Hence the sector is exactly
\[
\left\{\|G\|_{\mathrm{op}}\ge t\right\}
\cap
\left\{\|\wedge^2G\|_{\mathrm{op}}
      \ge t\|G\|_{\mathrm{op}}\right\}.
\]
Both conditions are closed.

The cheapest implementation is a three-dimensional variant avoiding exterior-algebra infrastructure:
\[
\operatorname{adj}(G)=G^2-e_1(G)G+e_2(G)I.
\]
Its eigenvalues are \(\lambda_2\lambda_3,\lambda_1\lambda_3,\lambda_1\lambda_2\), so
\[
\|\operatorname{adj}(G)\|_{\mathrm{op}}=\lambda_1\lambda_2.
\]
Since the adjugate is polynomial in the available elementary-symmetric functions, continuity is immediate.

Route (b), using only signs of \(q(t)\) and \(q'(t)\), is false. For example, at \(t=4\), spectra \((5,2,1)\) and \((7,6,5)\) both give \(q(t)<0\) and \(q'(t)>0\), but only the second has at least two eigenvalues above \(t\). A full Sturm-chain argument could work, but is substantially heavier.

**FACT vs INFERENCE:** FACT—the guarded compound/adjugate inequalities exactly characterize \(\lambda_2\ge\kappa^2\). INFERENCE—the adjugate formulation is the cheapest Borel proof with the stated library.

For the proposed architecture, a rank-stratum dichotomy is necessary—or equivalently, a global estimate retaining \(s_2\)-dependence. The complement \(s_2<\kappa\) is a genuinely separate integrability obligation: it is not absorbed by the Layer-2 weight \(\sigma_{\min}^{-a}\) with \(a<1\).