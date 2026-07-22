1. **KNOW: crux is needed but not derivable—and generally false.** At \(\delta=1\), product transport requires
\[
R(\sigma u)=u_pR(q(u)).
\]
For canonical centers at \(J=0\),
\[
\mathrm{center}=\{q\in\mathrm{layerCoords}(S):\operatorname{col}(q)<\mathrm{widthMinUpto}(S)\},
\]
so
\[
\mathrm{center}\subseteq\mathrm{supportAt}=\mathrm{layerCoords}(S).
\]
The reverse inclusion requires the additional fact
\[
\mathrm{widthMinUpto}(S)=d_S,
\]
which is false for general widths: `widthMinUpto` is a running minimum.

Counterexample: take \(i\in\mathrm{supportAt}\setminus\mathrm{center}\), \(a\in\mathrm{supportAt}^{c}\), and \(R(u)=u_i u_a\). This satisfies the new invariant using \(c_i(u)=u_a\), but under identity shear,
\[
R(\sigma u)=u_i u_a\neq u_pu_i u_a=u_pR(q(u)).
\]
Thus closure needs an additional construction identity saying the actual residual has zero effective support outside `ed.center`; no such fact follows from the invariant. **Open dependency.**

2. **KNOW: case-2 state advance is \((S,J)\mapsto(S,J+1)\); hence the child support is always \(C'=\mathrm{layerCoords}(S+1)\). But conjunct B does not follow.**

Writing
\[
c_i(v)=\sum_{a\in C^c}v_a h_{i,a}(v),
\]
the conditional \(\delta=1\) candidate is
\[
c'_a(u)=\sum_{i\in C}q_i(u)h_{i,a}(q(u)),\qquad a\in C',
\]
with zero coefficients elsewhere. This requires all \(a\notin C'\) terms to vanish and still does not establish `DeeperMultilinear` over \(C'^c\). Indeed \(R=u_pu_a\), \(a\in C'\), gives \(R'=u_a\), whose only possible coefficient is effectively \(1\); this cannot be `DeeperMultilinear` because such functions vanish when all \(C'^c\)-coordinates vanish.

For \(\delta=0\), if \(\sigma\) fixed \(C'\), the candidate would be \(c'_i=c_i\circ\sigma\). Pivot preservation alone does not imply this. The permitted triangular shear \(u_i\mapsto u_i+u_p\) sends \(R=u_i u_p\) to \(u_i u_p+u_p^2\), not supported on \(C'\). Thus self-propagation is **false from the stated hypotheses**; it needs stronger Let-block/shear and residual identities.

3. **NO.** On `univ`, `DeeperMultilinear c Cᶜ` does imply that \(c\) ignores \(C\), hence ignores `ed.center` when `ed.center ⊆ C`. But the old engine also needs the residual sum itself supported on `ed.center`. The new support is larger, so spectator terms obstruct divisibility. Transfer works only after proving `supportAt = ed.center` or an equivalent effective-support identity.