Verdict: the edge preserves the expected RLCT, but the proposed clean proof is wrong. Do not build the advertised finite-charge brick; either build a logarithmic/joint corank-one lemma or report a scope change.

1. Q1 — truth of \(T\)

Under the intended induction hypothesis for the reduced comparator, \(T\) should remain true for the strict inequality
\[
c'<\tfrac12\minAdm.
\]
The edge changes the pole multiplicity, not the RLCT.

Indeed, write \(r=b-s=\operatorname{rank}K\). At the edge \(\rho=a+b-1\), the rank-\((b-s)\) sector has combined codimension
\[
s(\rho-b+s)+a(b-s)
 =s(a-1+s)+a(b-s)
 =ab+s(s-1).
\]
Its candidate RLCT contribution is therefore
\[
\frac{ab+s(s-1)}2.
\]
Both \(s=0\) and \(s=1\) attain \(ab/2\); all \(s\ge2\) are strictly better. The corank-one tie produces a logarithm.

Concretely, if \(\sigma=\sigma_{\min}(K)\), then near rank \(b-1\)
\[
dA_{\rm cor}\,\det(KK^\top)^{-a/2}
 \sim \sigma^{a-1}\sigma^{-a}\,d\sigma
 =\frac{d\sigma}{\sigma}.
\]
The bounded \(\Gamma\)-box cuts this off at a scale
\[
\tau^2\asymp w+\lVert\eta_C\rVert^2,
\]
where \(\eta_C\) is the newly transverse \(C\)-component. Thus the honest result has a factor resembling
\[
1+\log\frac1{\tau},
\]
rather than an infinite constant. Since \(c'\) is strictly below threshold, choose \(\delta>0\) with
\[
c'-\frac{ab}{2}+\delta
  <\frac12\minAdm-\frac{ab}{2},
\]
and absorb the logarithm using
\[
1+\log(1/R)\le C_\delta R^{-\delta}.
\]
So \(T\) survives, but generally with an arbitrarily small exponent loss in the reduction.

Strictly speaking, the displayed setup alone lacks sufficient hypotheses on \(\widetilde Q\), \(w\), and the transverse \(C\)-map to state this as a Lean theorem. A uniform corank-one transversality or the appropriate rank-sector IH must be explicit.

2. Q2 — clean versus hard

The claimed exact clean estimate with a finite constant and exponent exactly \(c'-ab/2\) is false in general.

The smallest edge case \(a=b=\rho=1\), with \(C_{\rm cross}=0\), gives
\[
H_p(w)=\int_{-1}^1\int_{-1}^1
       (w+x^2y^2)^{-p}\,dx\,dy
 \asymp w^{1/2-p}\log(1/w)
\]
for \(p>1/2\). Hence
\[
H_p(w)\not\le C\,w^{-(p-1/2)}
\]
with \(C\) independent of \(w\). Only
\[
H_p(w)\le C_\delta w^{-(p-1/2+\delta)}
\]
holds.

A sufficiently nondegenerate \(C\)-integration can remove this logarithm—for example, \(c+xy\) permits the change of variable \(c'=c+xy\). But proving that in the matrix problem requires a uniform statement that \(C\) supplies the \(a\) fragile directions near every rank-\((b-1)\) point. That is already a joint corank-one determinantal/transversality argument.

You may not need the entire deep-case all-rank resolution: only ranks \(b\) and \(b-1\) are critical at the edge. But this is not the advertised bare “clean brick.” If the architecture requires an exact \(ab/2\) peel with a finite front constant, STOP and report the scope change. An edge-specific logarithmic brick with exponent slack is viable.

3. Q3 — polar route

Your objection is exactly correct:
\[
\int_{S^{ab-1}}\|\Omega K\|_F^{-ab}\,d\Omega
 =\omega_{ab-1}\det(KK^\top)^{-a/2}.
\]
Therefore the proposed \(J\) is logarithmically divergent at the edge.

To salvage polar coordinates one must retain:

- The finite radial cutoff \(0\le s\le s_{\max}(\Omega)\) coming from the \(\Gamma\)-box.
- The \(C\)-shift \(C_{\rm cross}+s\Omega K\).
- The residual scale \(w\).

After \(u=s\|\Omega K\|\), the upper limit is \(s_{\max}\|\Omega K\|\); it tends to zero when \(K\) degenerates and cancels the apparent determinant singularity. The resulting angular factor is regularized, roughly
\[
\min\!\left\{w^{-c'},\,
 \|\Omega K\|^{-ab}w^{ab/2-c'}\right\},
\]
not the bare \(\|\Omega K\|^{-ab}\). Its edge behavior is logarithmic unless the transverse \(C\)-integration is retained jointly.

Thus the literal polar certificate is invalid.