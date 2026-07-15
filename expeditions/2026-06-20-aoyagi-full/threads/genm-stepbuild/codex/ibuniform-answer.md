## 1. VERDICT

**NON-UNIFORM.** For the stated unweighted corner comparator, the rank-zero deep stratum has front/comparator ratio \(\asymp r^{-ab}\) at fixed \(q<T1_q\).

## 2. THE DECIDING COMPUTATION

Let \(k=\rho-m\), with the \(k\) lost singular values comparable to a polar radius \(r\).

[Established normal-form calculation.] The comparator fibre is

\[
\int_{\mathbb R^{um}\times\mathbb R^{uk}}
 (|y|^2+r^2|w|^2)^{-q}\,dy\,dw
 \asymp r^{-\beta_C},
\qquad
\beta_C=(2q-um)_+,
\]

with a logarithm when \(2q=um\). Tail codimension \(\kappa\) therefore gives radial density \(r^{\kappa-1-\beta_C}\).

For the front charge, refine by \(\operatorname{rank}(A_{\rm cor}|_{\mathrm{surv}})=b-h\). Then

\[
\det(Q_bQ_b^\top)^{-a/2}\sim r^{-ah},
\]

while that rank stratum has tubular codimension

\[
h(m-b+h).
\]

Thus its excess over the comparator is

\[
\Delta_h=ah-h(m-b+h)
       =h(a-m+b-h).
\]

Positive \(\Delta_h\) gives ratio \(r^{-\Delta_h}\); equality gives an unbounded logarithm. Here
\(\max(0,b-m)\le h\le\min(b,k)\).

The decisive case is \(m=0\), where necessarily \(h=b\):

\[
\Delta_b=ab.
\]

Indeed, under \(Z=rZ_\ast\),

\[
K_{\rm front}(rZ_\ast)=r^{-(ab+2q)}K_{\rm front}(Z_\ast),\qquad
K_{\rm comp}(rZ_\ast)=r^{-2q}K_{\rm comp}(Z_\ast).
\]

Hence

\[
\frac{K_{\rm front}}{K_{\rm comp}}\asymp r^{-ab}\to\infty,
\]

while the respective radial densities are

\[
r^{\kappa-1-ab-2q},
\qquad
r^{\kappa-1-2q}.
\]

Example: \(M=(4,4,4,4)\), \(t^\star=2\), \(j=1\), so \(u=3\), \(a=b=1\), \(\rho=4\), \(T1_q=5\). At the \(Z=0\) stratum, \(\kappa=16\); with fixed \(q=1\), both integrals converge, but their ratio is \(r^{-1}\).

[Normalization caveat.] Exact moving transformed boxes cancel the raw Jacobian mismatch \(r^{-bk}\). A fixed-box majorant does not. Nevertheless the rank-zero \(r^{-ab}\) excess above remains because `frontChargeIntegrand` contains the peeled determinant charge. Uniformity could only become plausible if the comparator carried that same charge.

## 3. THE RISK

A Lean theorem asserting tailwise domination by the present `cornerComparator` is false; it breaks at \(Z\to0\) before any endpoint limit. The scalar quotient \(I/J\) is trivially finite once both integrals are already known finite, so using it to prove \(I<\infty\) would be circular. A joint/decorated comparator retaining the determinant charge, or a separate deep-stratum resolution, is required.