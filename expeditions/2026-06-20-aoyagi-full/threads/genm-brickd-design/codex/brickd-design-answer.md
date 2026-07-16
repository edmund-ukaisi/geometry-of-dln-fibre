**Q1 — [FACT] Over-counting, not a product.** Put \(d_s=p(r-k)\) and \(q=c'-d_s/2\). [FACT] If \(q<0\), the integral is uniformly bounded; if \(q=0\), it grows logarithmically. [FACT] For \(0<q<kp/2\), write \(q=Lp/2+\delta\), \(0\le\delta<p/2\). Away from \(\delta=0\), its sharp scale dependence is
\[
\asymp\Bigl(\prod_{i=k-L+1}^{k}\lambda_i^{-p/2}\Bigr)\lambda_{k-L}^{-\delta}.
\]
[FACT] At \(\delta=0\), replace the last factor by \(1+\log(\lambda_{k-L+1}/\lambda_{k-L})\). Thus the largest weak scales are exhausted first; for \(q<p/2\), the answer is simply \(\lambda_k^{-q}\), independent of \(\lambda_1\). [FACT] The bound \(\lambda_1^{-\alpha'/2}\), with \(\alpha'/2>q\), therefore over-counts—sometimes drastically. [FACT] There is no general factorization \(\prod_i\lambda_i^{-a/2}\); that product is the weak singular determinant to power \(-a\), whereas \(\prod_i\lambda_i^{-a}\) would have twice the claimed exponent.

**Q2 — [FACT] No: the two determinants measure different degeneracies.** Let \(P=Q_pQ_p^\top\), \(S=Q_bQ_b^\top\), and \(R=Q_pQ_b^\top\). [FACT] When \(P\) is invertible,
\[
\det G=\det P\;\det(S-R^\top P^{-1}R)
=\det P\;\det\!\bigl(Q_b(I-\Pi_p)Q_b^\top\bigr).
\]
[FACT] The second determinant—the transverse Schur complement—is the honest weak determinant relative to the pivot. [FACT] By contrast, \(\det(S)^{-a/2}\) is the exact Jacobian from \(\Gamma\mapsto\Gamma Q_b\), not the full stacked spectral divergence. [FACT] Even with all strong eigenvalues bounded, these are not comparable: for \(Q_p=(1,0)\), \(Q_b=(1,t)\), \(S\sim1\) while the weak eigenvalue and Schur complement are \(\asymp t^2\).

**Q3 — [INFERENCE] Incomplete as stated.** [FACT] The shear and determinant extraction are non-circular and require no floor on \(\mathrm{hsQ}\). [FACT] But determinant integrability alone cannot control the remaining projector-dependent negative power: \(Q_b\) may be large and full-rank while its rowspace approaches the pivot rowspace. [INFERENCE] A new joint incidence/integrability lemma could complete mechanism II; without it, (D) does not follow. [FACT] If that lemma is proved, mechanism I is unnecessary; its \(k=1\) estimate is only an optional local bound, not coverage missing from II.

**Q4 — [FACT] The coupled projector estimate is the hard step.** One must prove a weighted bound of the form
\[
\int \det(Q_bQ_b^\top)^{-a/2}\,
\Phi\!\bigl(Q_p(I-\Pi_b)\bigr)\,dA_{\rm cor}
\lesssim \Phi_{\rm red}(Q_p).
\]
[FACT] Negative powers reverse the contraction inequality, so \(Q_p(I-\Pi_b)\le Q_p\) gives the wrong direction. [FACT] Tonelli permits reordering, but the integrals cannot generally be factored; alignment couples \(A_{\rm cor}\) to \(Q_p(z)\). [FACT] A supremum pull-out is unsound: along \(A=tA_0\), the determinant divisor scales as \(t^{-ab}\), and projector constants may also blow up near rowspace alignment.

**Q5 — [FACT] Logarithmic boundary; separate top case.** For \(d=ab\),
\[
\int (w+\lVert y\rVert^2)^{-d/2}dy\asymp 1+\log(1/w).
\]
[FACT] Hence the clean shift formula works only for \(c'>ab/2\); at equality one must retain the logarithm or absorb it using an arbitrarily small positive exponent and the strict induction margin. [FACT] For \(c'<ab/2\), use the no-shift estimate \(\int_\Gamma(w+\cdots)^{-c'}\le Cw^{-c'}\). [FACT] When \(a=0\), there is no corner, determinant gain, or inductive progress, so it should be a separate base case.

**Q6 — [INFERENCE] Hybrid, Schur-led.** [INFERENCE] The cleanest formal proof uses mechanism II plus minor-chart stratification and local radial estimates, not a global spectral peel. [FACT] The hardest lemma is the coupled weighted Schur-projector estimate in Q4. [FACT] It can be formalized using finitely many algebraic maximal-minor charts; no globally smooth SVD or eigenbasis is needed.

[INFERENCE] The likeliest break is treating \(\det(Q_bQ_b^\top)\) as though it controlled pivot–corank transversality. [FACT] The cheapest test is \(u=a=b=1\), \(Z=I_2\), \(Q_p=(1,0)\), \(Q_b=(x,y)\): the proposed divisor is \((x^2+y^2)^{-1/2}\), while the Schur determinant is \(y^2\). Checking the joint local integral near \(y=0\) settles the missing absorption lemma.