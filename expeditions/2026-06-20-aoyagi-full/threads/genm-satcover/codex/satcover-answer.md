1. **VERDICT: (B), with one correction: the residual rank stratification is not always vacuous.**

2. Exact block algebra:

\[
a=(M_0-M_1)_+,\qquad b=(M_1-M_0)_+,\qquad ab=0.
\]

- \(b=0\): \(Q_b\) and \(B\) are empty, \(\det(Q_bQ_b^T)=1\), \(\Pi_b=0\), \(N=I\), and \(W=Q_p\). The corank incidence disappears, but \(\operatorname{rank}(Q_p)=l\) can remain nontrivial.
- \(a=0\): \(C\) vanishes and \(\det(Q_bQ_b^T)^0=1\), but \(Q_b\) generally remains. Thus \(W=Q_pN\) may also remain nontrivial.
- \(M_0=M_1\): \(a=b=0\); both \(Q_b\) and \(C\) vanish.

Hence the determinant divisor is always a unit, but the blanket claim that the entire \(W\)-stratification becomes content-free is false. Nevertheless Brick D does not cover the boundary as stated: its scope \(a+b\le M_2\) and strict-shell hypotheses are unavailable, and when \(a=0,\ b>M_2\), its full-row-rank \(Q_b\) charts do not even exist.

3. Put \(u=\min(M_0,M_1)\) and \(R=\operatorname{redChain}(u,M)\). The needed separate saturated lemma is

\[
G(\operatorname{shell}_{j=r};c')
 \le C_{\mathrm{sat}}\,
 \operatorname{comparator}(R).\operatorname{integral}(c'),
\qquad C_{\mathrm{sat}}<\infty .
\]

There is no exponent shift because \(q=c'-ab/2=c'\). The lower-arity hypothesis

\[
d<\frac{\minAdm(R)}2
\Longrightarrow
\operatorname{comparator}(R).\operatorname{integral}(d)<\infty
\]

is applied at \(d=c'\). Indeed, the recursion candidate \(t=u\) gives exactly

\[
\minAdm(M)\le ab+\minAdm(R)=\minAdm(R).
\]

Thus \(c'<\minAdm(M)/2\) implies \(c'<\minAdm(R)/2\). This is a genuinely separate endpoint/pivot reduction, even if packaged under a common wrapper with Brick D.

4. For non-base arity, the subset estimate remains circular:

\[
G_{\mathrm{sat}}\le\operatorname{Box}(M)
\]

requires finiteness of the induction’s current level-\(M\) goal. Saturation does not identify the shell with the reduced object. It is non-circular only at the banked three-width base.

5. Corrections:

- “Exactly one of \(a,b\) is zero” fails when \(M_0=M_1\): both are zero.
- \(M=(2,1,2)\) does **not** violate \(a+b\le M_2\): \(1\le2\). It only violates the stronger quoted coverage bound.
- No sweep is needed for \(\minAdm(M)\le\minAdm(R)\); it follows directly from the recursion at \(t=u\).