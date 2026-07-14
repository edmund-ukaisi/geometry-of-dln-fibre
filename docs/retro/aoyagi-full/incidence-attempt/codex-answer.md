I independently verified F1–F3. For F4, \(M(3,3,4)=\min(9,8,9,12)=8\), hence RLCT \(=4\); the claimed “thresholds-only \(=3\)” cannot be independently checked because that recurrence is not specified.

### Q1

**Verdict:** Aoyagi does not contain the layer-peeling estimate.

**OBSERVED FACT:** Lemma 1 and Lemma 2/Theorem 3 give local germ equivalences; the recursive charts resolve the entire product ideal and recover its RLCT. None disintegrates the integral by \(z\) or bounds one layer by a shorter-chain integral.

**INFERENCE:** A pointwise/uniform-in-\(z\) peeling inequality is strictly additional. However, the displayed version has both sides integrated over \(z\) and an unrestricted \(K_j\). Literally, if \(0<R<\infty\) and \(L<\infty\), it follows vacuously with \(K_j=L/R\); if \(R=\infty\), it is useless. The genuinely different statement is therefore a pointwise-in-\(z\) bound, or one with specified uniform dependencies for \(K_j\).

### Q2

**Verdict:** (a)–(b) are locally repairable; (c) requires retaining Aoyagi’s full weights; (d) is the genuinely new peeling difficulty.

- **(a) \(P^{-1}\): OBSERVED FACT.**  
  \(\Gamma^\sharp=\Gamma-CP^{-1}B\) has Jacobian \(1\), while \(B=PD\) gives
  \[
  dB=|\det P|^b\,dD.
  \]
  Norm-comparison constants grow like powers of \(\sigma_{\min}(P)^{-1}\). A uniform floor \(\sigma_{\min}(P)\ge\delta\) fixes this. Without it one needs dyadic singular-value strata or determinantal blow-ups; a codimension-\(k\) blow-up has Jacobian \(|u|^{k-1}\). This is resolution labour, not a consequence of “\(P\) is invertible”.

- **(b) Moving \(Q_p\): OBSERVED FACT.**  
  On a chart where a \(u\times u\) minor \(X_I\) of \(X=Q_p(z)\) is floored, normalize using \(P'=PX_I,\ C'=CX_I\):
  \[
  dP'\,dC'=|\det X_I|^{u+a}\,dP\,dC.
  \]
  This is uniform only while \(|\det X_I|\ge\delta\). Covering rank loss requires minor shells and proving that their determinant powers are absorbed by the divisor/RHS. That global uniform absorption is additional content.

- **(c) Divisors: OBSERVED FACT + INFERENCE.**  
  Aoyagi tracks the individual \(b_i\) and their shared exceptional factors. Factoring a scalar common divisor has Jacobian \(1\), but discards this support-sharing information. Reproducing \(\operatorname{diag}(b_i)\) and all blow-up charts fixes the issue by labour. Collapsing it to `commonDivisor` with exactly the claimed exponent shift requires a new weighted comparison theorem; F4, if accepted, shows why it cannot be assumed.

- **(d) Incidence: VERIFIED FACT.**  
  In F2,
  \[
  \det(YY^\top)=1+|t|^2,\quad
  \det X(I-\Pi_Y)X^\top=\frac{|t|^2}{1+|t|^2},\quad
  \det Y(I-\Pi_X)Y^\top=|t|^2.
  \]
  Thus bounded Gram units cannot remove incidence. Principal-angle/determinantal blow-ups can resolve it, but a uniform fiber estimate after integrating layer variables is genuinely new relative to Aoyagi.

### Q3

**Verdict:** F2 is strong consistency evidence, but not evidence that incidence is the only obstruction unless (a)–(c) have already been resolved.

**VERIFIED FACT:** Here
\[
F=(p+\beta)^2+(c_0+\gamma)^2+(\beta^2+\gamma^2)|t|^2,
\]
and \(\beta\) remains bounded away from zero. Hence the transverse RLCT is exactly \(4/2=2\). F1 also checks directly: \(M(2,2,3)=\min(4,4,6)=4\), while the reduced codimension is \(3\).

A precise sufficient uniform incidence estimate is the following. Put \(X=Q_p(z)\), \(Y=A_{\rm cor}Z(z)\),
\[
D=XY^\top(YY^\top)^{-1},\qquad S=X(I-\Pi_Y),\qquad q=c'-ab/2.
\]
The translations
\[
B'=B+PD,\qquad \Gamma'=\Gamma+CD
\]
have Jacobian \(1\), and integration over all \(\Gamma'\) gives
\[
C_{c',a,b}\det(YY^\top)^{-a/2}
\bigl(\|PS\|^2+\|B'Y\|^2+\|CS\|^2\bigr)^{-q}.
\]
What is needed is a \(z\)-uniform bound of its remaining \(A_{\rm cor},P,C,B'\) integral by
\[
K_j\bigl(g(z)^2\|X\|^2\bigr)^{-q},
\]
including the translated-box condition \(B'-PD\in\mathcal B\). The equivalent transverse determinant is related by
\[
\det(YY^\top)\det\!\bigl(X(I-\Pi_Y)X^\top\bigr)
=\det(XX^\top)\det\!\bigl(Y(I-\Pi_X)Y^\top\bigr).
\]

**INFERENCE:** This parameter-uniform pushforward estimate is not extracted from Aoyagi by bounded bookkeeping: her blow-ups jointly mix base and fiber variables. A base-preserving, fiberwise resolution with uniform constants would be new mathematics for the peeling architecture.

### Q4

**Verdict:** Yes. This is the clean alternative if only whole-chain finiteness is required.

**OBSERVED FACT:** Aoyagi’s global resolution already gives finiteness for every \(c'<T_1\). Formalizing it requires the complete \(\operatorname{diag}(b_i)\) invariant, all Case 1(1)/1(2)/2 branches, the coordinate maps in Eqs. (1)–(5), every blow-up Jacobian, and a finite assembly of local charts. Germ ideal equality must also be converted locally to two-sided norm comparison using bounded analytic coefficient matrices.

**INFERENCE:** This is extensive but bounded resolution labour and avoids \((*_{T1})\) entirely.

The minimal genuinely new requirements for a meaningful, pointwise peeling theorem are: (1) a uniform parameterized incidence/pushforward estimate of the form above, including singular-\(P\) and rank-minor strata; and (2) a theorem showing that Aoyagi’s rowwise coupled \(b_i\) weights imply the proposed scalar `commonDivisor` bound with the exact \(ab/2\) shift. For the literal already-\(z\)-integrated inequality with unrestricted \(K_j\), neither is logically required once both integrals are known finite.