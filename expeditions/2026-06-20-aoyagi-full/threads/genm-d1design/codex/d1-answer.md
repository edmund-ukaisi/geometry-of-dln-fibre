## Q1

**1a — ARGUED: no banked route.** In the hard range \(c'>au/2\), applying (G) to \(C\in\mathbb R^{a\times u}\) gives
\[
\det(\widetilde Q\widetilde Q^\top)^{-a/2}
\Bigl(w+\|\gamma Q_b(I-P_{\widetilde Q})\|_F^2\Bigr)^{-(c'-au/2)}.
\]
The undecorated exponent is safe:
\[
c'-\frac{au}{2}
<\frac{\minAdm(\redChain_u M)-a(u-1)}2
\le \frac{\minAdm(\redChain_u M)}2,
\]
using \(\minAdm(M)\le a+\minAdm(\redChain_uM)\). But the determinant records the missing Jacobian; \(au/2\) is not a disposable net charge.

Every other banked ordering has the same obstruction:

- Integrate \(\gamma\) first: obtain \(\|Q_b\|^{-a}\), with \(Q_b\) a product row.
- Then integrate \(C\): additionally obtain a transverse product-Gram.
- Integrate \([C\mid\gamma]\) together: obtain the Gram of \(\binom{\widetilde Q}{Q_b}\).
- Drop the transverse term: \(\int\|\widetilde Q\omega\|^{-a}d\omega=\infty\) for \(a\ge u\).

Thus no ordering using only (G,Q,C,R,S) reaches plain hIH.

**1b — PROVEN:** (Q) cannot be applied to \(\widetilde Q=W'Z_{\rm deep}\) as though \(\widetilde Q\) were free. Conditional integration over free \(W'\) either requires \(Z_{\rm deep}\) uniformly nondegenerate or transfers another determinant/rank weight onto \(Z_{\rm deep}\). “Recurse one level” therefore preserves the Gram decoration. Plain hIH cannot receive it. Only terminal cases with no deep factor, or uniformly nonsingular deep factors, are one-level qbox cases.

**1c — ARGUED:** this is genuinely new analytic content.

Minimal missing lemma: for \(W'\in\mathbb R^{u\times M_2}\), \(y_b\in\mathbb R^{1\times M_2}\), \(Z_{\rm deep}\in\mathbb R^{M_2\times q}\), \(\widetilde Q=W'Z_{\rm deep}\), \(Q_b=y_bZ_{\rm deep}\), and \(a\ge u\), prove joint boxed finiteness of
\[
\det(\widetilde Q\widetilde Q^\top)^{-a/2}
\Bigl(\|P\widetilde Q\|_F^2+
\|\gamma Q_b(I-P_{\widetilde Q})\|_F^2\Bigr)^{-(c'-au/2)}
\]
for every \(au/2<c'<\minAdm(M)/2\); this is a pivot-Gram-decorated reduced-chain IH.

**VERDICT: OPEN-PROBLEM — the \(a\ge u\) arm requires a decorated/coupled IH.**

## Q2

**2a — PROVEN:** pointwise the map is submersive, but the measure problem still contains joint product-corank incidence. Put
\[
m=M_0,\quad n=m+b=M_1,\quad k=M_2.
\]
At fixed full-rank \(X\), \(D_Y(XY)(\delta Y)=X\delta Y\) is surjective, so the local codimension is \((m-r)(k-r)\). However, tubes approaching \(\rank X=s<m\) have joint codimension
\[
C_s=(m-s)(n-s)+(s-r)(k-r),\qquad r\le s\le m.
\]
They dominate whenever \(C_s<C_m\). For \(m=n=k\), \(r=m-\ell\), and \(h=m-s\),
\[
C_s=h^2+(\ell-h)\ell,
\qquad
\min_s C_s=\ell^2-\lfloor\ell^2/4\rfloor.
\]
This is exactly the joint product-corank codimension. Excluding the exact locus \(\det P=0\) removes a null set, not its singular tubes.

**2b — PROVEN:** the proposed fold is false in general. A density singularity is normal to a nonzero rank-deficient \(W_0\), whereas \(\|WZ_{\rm deep}\|_F\) need not vanish there. Choose \(Z_0\) with \(W_0Z_0\ne0\); on a tube around \((W_0,Z_0)\), the right-hand side remains bounded while \(\rho(W)\) is unbounded. Degenerate \(Z_{\rm deep}\) only makes the proposed majorant larger; generic \(Z_{\rm deep}\) exposes the failure. The inequality can work only after sectors ensuring that the loss detects the relevant normal coordinates.

**2c — ARGUED:** the equality
\[
\min_s\bigl[(m-s)(n-s)+\minAdm(\redChain_sM)\bigr]=\minAdm(M)
\]
settles the arithmetic, not the measure domination. The required atlas must resolve the joint \((X,Y)\) multiplication map, its boundary tubes, Jacobians, and downstream loss. This is not supplied by the ordinary determinantal resolution of \(W\) or by plain hIH.

Minimal missing lemma: for boxed \(X\in\mathbb R^{m\times(m+b)}\) on a nonzero-minor chart, \(Y\in\mathbb R^{(m+b)\times k}\), and a boxed deep product \(Z\), prove
\[
\int\|XYZ\|_F^{-2c}\,dX\,dY\,dZ<\infty
\quad\text{when}\quad
2c<\min_{0\le s\le m}
\bigl((m-s)(m+b-s)+\minAdm(s,k,\ldots)\bigr),
\]
with every \(s\)-chart dominated by the plain IH for \((s,k,\ldots)\).

The \(b=0\) arm is not a clean transpose. Its tall map is injective, not surjective. The one-shot qbox is legitimate exactly when
\[
M_2<M_0-M_1+1,\quad\text{i.e. }M_2\le a.
\]
When \(M_2>a\), that qbox integral diverges; further recursion again requires a carried Gram/joint-resolution theorem, not plain hIH.

**VERDICT: OPEN-PROBLEM — the low-\(A\) pointwise fold is unsound, and the high-\(A\) arm needs a new joint pushforward theorem.**

Cheapest discriminating computation: in the \(2\times2\) square case evaluate
\[
\rho(\operatorname{diag}(1/2,\varepsilon))
=\int_{X:\,X^{-1}W_\varepsilon\in\Box}
|\det X|^{-2}\,dX.
\]
Its \(\log(1/\varepsilon)\) growth, while \(W_\varepsilon e_1=(1/2,0)^\top\), simultaneously disproves the fold and detects the boundary joint incidence.