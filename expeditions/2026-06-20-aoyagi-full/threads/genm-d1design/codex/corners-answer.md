## Corner (i)

(a) **PROVEN.** For \(\|\Theta\|_F=1\),
\[
\|P\Theta\|_F^2\ge \sigma_{\min}(P)^2.
\]
This is arity-independent. It is only pointwise in \(P\); the full invertible box need not have a uniform positive lower bound for \(\sigma_{\min}(P)\).

(b) **PROVEN charge; NOT absorbed by plain IH.** Since \(ab=a\),
\[
s:=c'-a/2<\minAdm(\operatorname{redChain}_uM)/2.
\]
But \(w=\|[P\mid B_{12}]A_1Z\|_F^2\) is initially the product chain
\[
(u,u+1,M_2,\ldots),
\]
not a free first layer of \(\operatorname{redChain}_uM\). Collapsing
\[
F=[P\mid B_{12}]\in\mathbb R^{u\times(u+1)},\qquad
A_1\in\mathbb R^{(u+1)\times M_2}
\]
to \(FA_1\in\mathbb R^{u\times M_2}\) has singular pushforward density near source-rank boundaries. Plain hIH supplies neither this change of variables nor a uniform outer bound.

(c) **PROVEN conditional on the collapse atlas.** Once a chart exposes an unweighted reduced product, every degeneration of \(\widetilde Q\)—including simultaneous deep rank-drop—is exactly covered by hIH at charge \(s\). Its shell law may be much worse than \(\rho^{uq-1}\), but cannot exceed the reduced-chain threshold. No extra determinant weight may remain.

**VERDICT: NEEDS-EXTRA-MECHANISM.** Minimal missing mechanism: a finite source-incidence atlas for
\[
(F,A_1)\in\mathbb R^{u\times(u+1)}\times\mathbb R^{(u+1)\times M_2},
\]
with pure-monomial exceptional Jacobian, whose \(s\)-strata reduce to unweighted hIH for \(\operatorname{redChain}_sM\) at the corresponding shifted charge.

**Cheapest discriminating computation.** For \(M=(2,2,1,3)\), \(u=a=b=1\),
\[
\widetilde Q=xy,\qquad
\int |x|^{-2s}\|y\|^{-2s}\,dx\,dy<\infty\iff s<\tfrac12,
\]
not \(s<uq/2=3/2\). Yet \(\minAdm(M)=2\) and \(s=c'-1/2<1/2\): hIH gives exactly the correct product-shell threshold.

## Corner (ii)

(a) **PROVEN insufficient.** The inequality
\[
\int_{\Gamma\text{-box}}\mathrm{freed}^{-c'}\le
\operatorname{vol}(\Gamma\text{-box})\,w^{-c'}
\]
is valid but discards the normal volume of \(Q_b\to0\). The pivot-only cap need not reach \(\minAdm(M)/2\). Moreover, \((u,M_1,M_2,\ldots)\) is not a shorter chain, so plain layer-count hIH cannot directly prove its finiteness.

(b) **PROVEN required.** Resolution (b) is the sound resolution:
\[
\widehat Q=\binom{\widetilde Q}{Q_b},\qquad
G=[C\mid\gamma]\in\mathbb R^{a\times(u+1)},\qquad
\mathrm{freed}=\|P\widetilde Q\|_F^2+\|G\widehat Q\|_F^2.
\]
The atlas must track \((\operatorname{rank}\widetilde Q,\operatorname{rank}\widehat Q)\), or equivalent relative-row incidence—not merely total rank. When \(q\le u\), \(Q_b\to0\) may cause no total-rank drop at all.

(c) **PROVEN genuine window.** For \(M=(4,3,2)\),
\[
u=a=q=2,\quad \minAdm(M)/2=3,
\]
whereas the pivot-only chain \((2,3,2)\) has threshold \(2\). Thus the bounded-\(\Gamma\) majorant diverges for \(2\le c'<3\), while the true joint corner remains finite.

**VERDICT: NEEDS-EXTRA-MECHANISM.** Resolution (a) does not suffice; resolution (b) is required. Minimal missing mechanism: a joint relative-rank/source-incidence atlas for
\[
G\in\mathbb R^{a\times(u+1)},\qquad
\widehat Q=Y\,Z_{\rm deep}\in\mathbb R^{(u+1)\times q},
\]
whose exceptional Jacobians are pure monomials and whose strata reduce to plain shorter-chain hIH without any \(\|Q_b\|^{-a}\) weight.

**Cheapest discriminating computation.** In the same \((4,3,2)\) chart, the corner is comparable to
\[
\|X\|^2+\|\gamma\|^2\|r\|^2,
\quad X\in\mathbb R^4,\ \gamma,r\in\mathbb R^2.
\]
Its threshold is \(4/2+\min(2,2)/2=3\); dropping the bilinear term leaves threshold \(4/2=2\).