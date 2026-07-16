**Q1 — PROVEN arithmetic; analytic closure is not proven.** For full-row-rank \(Q_b\),
\[
\int d\Gamma\,(F+\|\Gamma Q_b\|^2)^{-c}
\asymp \det(Q_bQ_b^{T})^{-a/2}F^{-(c-ab/2)}.
\]
Thus the peel spends \(ab/2\) and hands \(c-ab/2\) to the reduced chain, giving exactly
\[
\frac{ab}{2}+\frac12\minAdm(t^*,n,n)=\lambda_n.
\]
For \(n=4,t^*=2,a=b=2\),
\[
2+\frac72=\frac{11}{2},\qquad \frac72=\frac32+2,
\]
so the complete arithmetic is \(2+\frac32+2=\frac{11}{2}\), without slack. On a rank-\(r\) stratum of \(Q_b\), however, only \(ar/2\) is spent in \(\Gamma\); the missing amount must be supplied by transverse determinantal variables. Consequently, the displayed equality proves the budget identity, not convergence on degenerate \(Q_b\). Also, the maximal-corank binding choice is \(b=\lceil n/3\rceil\), not \(\lfloor n/2\rfloor\); the stated ranges \(b=2\) for \(n=4,5,6\) and \(b=3\) for \(n=7,8\) agree with \(\lceil n/3\rceil\).

**Q2 — PROVEN for a free Gram variable; otherwise only an inference.** The exact Wishart criterion is
\[
\int_{X\in[-1,1]^{m\times q}}\det(XX^T)^{-s}\,dX<\infty
\quad\Longleftrightarrow\quad
s<\frac{q-m+1}{2}.
\]
Here \(m=b,\ s=a/2\). At the square first peel \(a=b\), this requires \(a<q-b+1\), which holds; for \(n=4\), \(1<3/2\). Thus a *free* \(Q_b\) has no residual Gram deficit, including its rank-deficient strata. But \(Q_b\) is itself a product and shares deeper variables with the reduced loss. The Wishart criterion therefore does not prove joint integrability. Keeping the weight attached removes the artificial Hölder \(p<4\) loss, but it creates a joint determinantal-incidence problem; the \(21/8\to3\) recovery is not an exact conserved “weight budget” established by arithmetic alone.

**Q3 — PROVEN gap for a single radial blow-up.** For \(a=b=2\) and \(\operatorname{rank}Q_b=1\), the map \(\Gamma\mapsto\Gamma Q_b\) has only \(ar=2\) active dimensions instead of \(ab=4\). On the radial exceptional divisor there remains
\[
\{\widehat\Gamma Q_b=0\},
\]
whose nonzero points have \(\operatorname{rank}\widehat\Gamma\le1\). Hence the angular quadratic is not coercive, and one radial coordinate for \(\Gamma\) does not resolve the singularity. Rank-one \(\Gamma\) is harmless when \(Q_b\) is full rank; the necessary center is the *joint* rank/kernel incidence. An ordinary reduced-chain induction does not automatically resolve it, although a stronger decorated flag/determinantal induction could. The first occurrence is \(n=4,a=b=2\), at the nominal budget \(2+7/2=11/2\).

**Q4 — PROVEN assessment of the proposed argument; completion is an inference.** Merely attaching the Gram determinant and assuming the reduced chain retains its unweighted threshold is not a complete proof. One must additionally prove closure of the resulting family of weighted integrals under all determinantal/kernel strata—equivalently, perform nested flag or determinantal blow-ups. Such an enhanced induction may well recover the sharp threshold with no numerical deficit, consistently with Aoyagi, but that conclusion does not follow from the single-peel accounting. Without that extra resolution theorem, one must either add the internal stratification or invoke Aoyagi directly.

**Verdict: GAP-AT-CORANK-2.**