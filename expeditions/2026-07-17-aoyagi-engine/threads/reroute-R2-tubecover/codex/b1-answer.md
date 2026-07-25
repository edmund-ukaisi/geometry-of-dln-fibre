The escape cone does not break the bound. The apparent value \(2\) at \(t e_4\) comes from freezing \(C_1\); it is not the local RLCT in the full 21-dimensional parameter space.

### Q1 — Verdict: \(\operatorname{rlct}_{t e_4}=4\) (PROVEN)

After permutations, take \(C_1=tE_{11}\) and write
\[
C_1=\begin{pmatrix}a&r\\ c&D\end{pmatrix},\qquad
C_2=\begin{pmatrix}u\\ V\end{pmatrix},\qquad a\neq0.
\]
Gaussian elimination and analytic coordinate changes give
\[
\|C_1C_2\|^2\asymp \|\widetilde u\|^2+\|SV\|^2,
\quad
S=D-ca^{-1}r,
\]
where \(\widetilde u\in\mathbb R^4\), \(S\in\mathbb R^{2\times2}\), and \(V\in\mathbb R^{2\times4}\). The first term contributes \(4/2=2\). A direct singular-value/Fubini calculation gives \(\operatorname{rlct}\|SV\|^2=2\), hence the total is \(2+2=4\). Thus it equals \(\tfrac12\minAdm=4\). The value \(2\) is only the RLCT of the slice obtained by fixing \(C_1=tE_4\); the remaining directions are not flat.

### Q2 — Verdict: no single permutation, but a finite piecewise permutation works (PROVEN for the stated cone)

No single row/column permutation sends the whole of \(E\) into the fixed valid cone: the four positions in \(W\) have row-degree pattern \((2,2)\), while their complement has row sizes \((3,1,1)\), so some \(W\)-axis must remain a \(W\)-axis. Instead partition \(E\) into four sectors \(E_w\), according to which \(w\in W\) realizes \(\max_W|x_w|\). For each \(w\), a row/column permutation can send both \(w\) and the otherwise-uncontrolled entry \(x_8\) into \(V\). Consequently, after harmlessly taking \(C\ge1\),
\[
\phi_w(E_w)\subseteq\{\max_W|x_w|\le C\max_V|x_v|\}.
\]
Thus \(E\) is not globally isometric to one valid sector, but is a finite union of pieces isometric to valid dominance sectors. Inclusion in the exact image of a particular chart additionally requires that the chart cover its declared dominance sector.

### Q3 — Verdict: \(\operatorname{rlct}(\mathrm{loss}|E)=4\) (PROVEN)

For \(A\subseteq B\),
\[
\operatorname{rlct}(f|A)\ge \operatorname{rlct}(f|B),
\]
because restricting the positive zeta integral cannot introduce an earlier pole. Hence, if \(R\) is the valid region with \(\operatorname{rlct}(f|R)\ge4\), then
\[
\operatorname{rlct}(f|E_w)
=\operatorname{rlct}(f|\phi_w(E_w))
\ge\operatorname{rlct}(f|R)\ge4,
\]
and finite-union/minimum logic gives \(\operatorname{rlct}(f|E)\ge4\). Conversely, \(E\) contains an open neighborhood of each sufficiently small \(t e_4\), whose local RLCT is \(4\), so \(\operatorname{rlct}(f|E)\le4\). Therefore it is exactly \(4\), not below the target.

### Q4 — Verdict: the lower bound survives (PROVEN)

The restricted zeta integrals—or equivalently the sublevel volumes—add with nonnegative coefficients:
\[
V(\varepsilon)=V_{\mathrm{covered}}(\varepsilon)+V_E(\varepsilon).
\]
There can be no cancellation of leading poles, so
\[
\operatorname{rlct}(f)
=\min\!\left\{
\operatorname{rlct}(f|{\rm covered}),
\operatorname{rlct}(f|E)
\right\}.
\]
Both terms are at least \(4\), and the escape term is exactly \(4\). Therefore noncoverage by the fixed atlas is a proof-completeness defect, not a counterexample to \(\operatorname{rlct}\ge4\).

### Q5 — Verdict: DETAIL-AT-SCALE artifact (PROVEN abstractly; formula-level implementation is an INFERENCE)

A \(W\)-pivot chart can be defined by transporting a valid \(V\)-pivot chart through the appropriate loss-preserving permutation. Coordinate permutations have constant Jacobian \(\pm1\), preserve the Frobenius loss, and preserve monomial Jacobians and normal crossings. Thus a pivot-adapted normalization closes the escape sectors. The inference is only that a particular rewritten “adaptive shear” formula exactly realizes this transported chart; that formula should still be checked.

**Final adjudication:** B1 is a positive-measure hole in the fixed-shear atlas, but it is not MONUMENT-ADJACENT and does not break \(\operatorname{rlct}\ge\tfrac12\minAdm\). It is a DETAIL-AT-SCALE artifact dissolved by a permutation-closed, pivot-adapted-normalization atlas.