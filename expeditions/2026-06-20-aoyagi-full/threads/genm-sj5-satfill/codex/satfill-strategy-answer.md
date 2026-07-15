## 1. VERDICT

**NEEDS-EXTRA-HYP.** The banked facts do not control degeneration of \(P\); \(m\le uM_2\) is insufficient.

## 2. OBSTRUCTION

Write \(R=\kappa\text{-rows}(A'_0)\). Although \(W=PR\in\mathbb R^{uM_2}\), the pushforward of \(dP\,dR\) is not bounded by Lebesgue measure \(dW\) near \(W=0\). Radially scaling \(P=tP_0\) gives
\[
dP\sim t^{u^2-1}dt,\qquad \|PRZ'\|^{-2c'}\sim t^{-2c'}.
\]
The comparator instead has \(v^{m-1-2c'}dv\). Matching the singularity requires at least
\[
m\le u^2.
\]
For fixed \(c'\), the failure window is
\[
u^2\le 2c'<m.
\]

Concrete permitted data:
\[
(u,M_0,M_1,M_2,N,m)=(1,1,1,2,2,2),\qquad c'=\tfrac34,
\]
with \(a=b=0\) and \(Z'=I_2\). Then
\[
L=(p^2\|r\|^2),\qquad \int |p|^{-3/2}dp=\infty,
\]
whereas the comparator is finite because
\[
\int_0^1v^{-1/2}dv<\infty,\qquad
\int_{[-1,1]^2}\|z\|^{-3/2}dz<\infty.
\]

**Required-but-unstated:** to make this a counterexample to the exact shell LHS, the shell must contain a positive-measure set of \(r\neq0\). Without shell information, actual falsity is not forced—but the banked tools certainly do not prove the claim. Realisability of \(m=2\) by the unstated definition of `minAdm` is likewise an inference; it is allowed by every stated hypothesis.

## 3. WHY T1 DOES NOT FIX IT

T1 supplies the exponent \(uM_2-1\) for Lebesgue measure on an independently integrated \(W\). It does not justify replacing the bilinear pushforward \((P,R)\mapsto PR\) by \(dW\); that pushforward is singular near degenerate \(P\). Thus the comparator’s `decLoss` cannot absorb the pivot energy using only \(m\le uM_2\).

## 4. LEAN-COST

About **150–250 lines** to formalize the scalar counterexample. The hardest step is proving the LHS improper integral diverges while both comparator factors are finite. A repaired general domination lemma would likely be **400+ lines** and require new product-map/singular-value analysis, plus at least an \(m\le u^2\)-type hypothesis.