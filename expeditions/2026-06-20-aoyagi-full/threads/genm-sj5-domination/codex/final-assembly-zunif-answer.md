**Q1.** Yes, but saturate at \(r=\min(a,b)\): use exact-\(j\) shells for \(0\le j<r\), then one final shell containing all \(Z\) with at least \(r\) small singular values. The \(M_2+1\) exact-count shells are also finite, but cuts \(t^\star+j\) are unavailable for \(j>r\); those shells must all use the zero-corner cut \(t^\star+r\). On each \(j<r\) shell, use finitely many rank-revealing coordinate-minor charts, not a globally chosen SVD basis: Cauchy–Binet gives a uniformly invertible \((M_2-j)\)-minor from \(\sigma_{M_2-j}\ge\varepsilon\). Uniform elimination in that minor should leave the \(j\) weak directions inside the deeper comparator, whose shell indicator can then be discarded before invoking the full-box IH. This conclusion requires an analytic chart lemma controlling constants, Jacobians, and box enlargement; it does not follow from the shell partition and charge inequality alone.

**Q2.** Yes, the determinant-monotonicity bound is correct. From \(ZZ^{\mathsf T}\succeq\varepsilon^2I\) one gets
\[
A_{\mathrm{cor}}ZZ^{\mathsf T}A_{\mathrm{cor}}^{\mathsf T}
 \succeq \varepsilon^2A_{\mathrm{cor}}A_{\mathrm{cor}}^{\mathsf T},
\]
and PSD determinant monotonicity gives the claimed factor \(\varepsilon^{2b}\). Hence, with extended-value conventions on the rank-deficient measure-zero locus,
\[
\operatorname{Wenn}(Z)\le \varepsilon^{-ab}\operatorname{Wenn}(I).
\]
The right-hand side is finite precisely under the stated condition \(a<M_2-b+1\); no additional uniformity hole occurs on shell \(0\).

**Q3.** For the full shift, the charge calculation closes every \(0\le j\le r\). Writing \(k_j=(a-j)(b-j)\), \(R_j=\minAdm(\mathrm{redChain}@ (t^\star+j))\), and \(M=\minAdm(M)\), one has \(k_j+R_j\ge M\). Therefore
\[
2\!\left(c'-\frac{k_j}{2}\right)<M-k_j\le R_j,
\]
which is exactly the strict IH exponent inequality. Shells with more than \(r\) small singular values use \(j=r\), where \(k_r=0\). However, a fixed reduced shift \(\theta k_j/2\) with \(\theta<1\) is not justified by this charge: it requires \((1-\theta)k_j<M-2c'\). Thus the borderline case closes only if \(\theta\) may be chosen sufficiently close to \(1\), or if a separate \(\theta\)-weighted charge inequality is available.

**Q4.** There is no infinite regress if the IH is used as stated. After the shell/chart reduction, invoke the full-box IH for the one-node-shorter comparator outright; do not reapply its internal per-\(Z\) estimate. If the induction proof is unfolded, chain arity decreases at every recursive call, which is the well-founded parameter; \(j\) is only a finite local branch index. The saturated branch \(j=r\) has zero freed-corner width, while all remaining rank degenerations are already included in the deeper IH. Reapplying the non-uniform conditional estimate instead of invoking the IH would recreate the gap, but that is a proof-assembly error.

**Q5.** **LABOUR — the riskiest spot is the adapted-minor chart lemma: uniform constants, box distortion, and measure/Jacobian control while identifying the residual exactly with an IH comparator.** No degenerate \(Z\) is missed by the saturated final shell, and the full-charge inequalities add correctly. The assembly is therefore mathematically credible but not formally closed until that analytic lemma is supplied; a fixed non-adjustable \(\theta<1\) would be a separate genuine exponent obstruction.