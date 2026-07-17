**Q1 — PROVEN: coupled incidence, not a clean reduced chain.** Although
\[
Q_b^\perp=Q_b(I-P_{\widetilde Q_p})
\]
is formally a matrix product, its right factor depends rationally on the shared deeper variables. In particular,
\[
Q_b^\perp\widetilde Q_p^{\,T}=0
\]
identically, so \(Q_b^\perp\) is neither free nor independent of the pivot tail. Moreover, \(\Gamma Q_b^\perp\) has leading width \(c\), whereas the claimed reduced chain begins with \(t^*\); these agree accidentally for \(n=4\), but not generally. Thus the ordinary plain/decorated DLN arity-IH does not apply without an additional relative quotient/principalization lemma.

**Q2 — generic arithmetic PROVEN; full exceptional-power claim NOT PROVEN.** Put \(\lambda_{\rm red}=\frac12\minAdm(t^*,n,n)\). Formally,
\[
\frac{au}{2}+\lambda_{\rm red}-c^*
=\frac{ct^*-c^2}{2}
=\frac{c(t^*-c)}2.
\]
Hence, except when \(t^*=c\), C-integration already “spends” more than the required \(c^2/2\). Exact accounting therefore requires the pivot/projected incidence to cost \(c(t^*-c)/2\); qbox-integrability cannot be interpreted as a nonnegative zero-cost decoration.

For \(n=4\),
\[
t^*=u=c=a=2,\qquad q=4,
\]
and
\[
\minAdm(2,4,4)=\min(8,7,8)=7.
\]
Thus the generic arithmetic is
\[
\frac{au}{2}+0+\lambda_{\rm red}
=2+0+\frac72=\frac{11}{2}=c^*.
\]
Here \(m=u=2,\ s=a/2=1\), and Wishart gives \(2s=2<4-2+1=3\). Its corank-one exceptional exponent is
\[
q-u-2s=4-2-2=0>-1.
\]
But on a deeper rank-\(k\) stratum the effective exponent is
\[
k-u-a=k-n.
\]
For \(n=4\), this is \(-1\) at \(k=3\) and \(-2\) at \(k=2\), so the conditional qbox sign fails. Transverse rank-stratum Jacobians may repair these powers, but proving that requires the missing joint resolution. Consequently the full inequalities \(a_i-2c'N_i>-1\) are not established by the banked lemmas.

**Q3 — PROVEN.** Nominally \(q=n\), so
\[
a<q-u+1\iff c<c+1
\]
passes. After the deeper tail has rank \(k\), however, \(q_{\rm eff}=k\), and the gate becomes
\[
c<k-t^*+1.
\]
For integral dimensions this holds only at \(k=n\); \(k=n-1\) is marginal and lower ranks fail. Thus the pivot-Gram recursion/marginal fold is mandatory. Any accumulated gate of the form \(2c\le q-u\) becomes \(2c\le c\), hence fails for \(c\ge2\).

**Q4 — PROVEN assessment.** Integrating \(C\) and avoiding a second gammaAtom is reasonable, but the proposed closure is incomplete. The minimal missing piece is a relative joint principalization theorem for
\[
\det(\widetilde Q_p\widetilde Q_p^T)^{-c/2}
\Bigl(\|P\widetilde Q_p\|^2+
\|\Gamma Q_b(I-P_{\widetilde Q_p})\|^2\Bigr)^{-d},
\]
uniform across all shared-tail rank strata, with the resulting exceptional powers checked against \(>-1\).

**GAP-AT-PROJECTED-TAIL-PRINCIPALIZATION**