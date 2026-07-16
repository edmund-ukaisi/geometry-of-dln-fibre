### 1. S1 — SOUND

Since \(Q_b=Q_{\mathrm{inr}}\) has full row rank, \(\mathrm{proj}\) is its row-space projector, so
\[
Q_{\mathrm{inr}}(I-\mathrm{proj})=0.
\]
Thus \(E_{\mathrm{tr}}=\|C\,Q_{\mathrm{inl}}(I-\mathrm{proj})\|_F^2\), independent of \(P,B_{12}\).

### 2. S2 — SOUND as an inequality; FLAWED as an automatic finiteness reduction

Pointwise in the extended nonnegative reals,
\[
(E_{\mathrm{top}}+E_{\mathrm{tr}})^{-q}\le E_{\mathrm{tr}}^{-q}
\qquad(q>0).
\]
But dropping \(E_{\mathrm{top}}\) can destroy convergence.

For example, take
\[
Q_{\mathrm{inr}}=(1,0),\quad Q_{\mathrm{inl}}=(0,1),\quad
P\in[1,2].
\]
Then \(E_{\mathrm{top}}=B_{12}^{2}+P^{2}\ge1\), while \(E_{\mathrm{tr}}=C^{2}\). The original integral is finite for every \(q>0\), whereas
\[
\int_{-1}^{1}|C|^{-2q}\,dC=\infty
\quad\text{for }q\ge\tfrac12.
\]

Generally, if \(C\in\mathbb R^{m\times a}\), \(\operatorname{rank}W=r\), and the \(C\)-box meets \(\ker(C\mapsto CW)\), the local threshold is \(2q<mr\). Without such a threshold, retaining \(E_{\mathrm{top}}\) may be necessary.

### 3. S4 — GENUINE MISMATCH

Yes. The resulting loss uses
\[
W=Q_{\mathrm{inl}}(I-\mathrm{proj}),
\]
which depends on \((z,A_{\mathrm{cor}})\), while the charge uses \(Z_{\mathrm{deep}}\). Identifying \(S=W\) breaks the charge; identifying \(S=Z_{\mathrm{deep}}\) breaks the loss. Moreover, the exponents are \(q\) versus \(c'\).

Matching ranks alone only matches local integrability thresholds. It does not control singular values, Jacobians, or the outer-parameter integral. A reconciliation would require additional structure such as a uniformly controlled factorization \(W=RZ_{\mathrm{deep}}\) and a compatible change of variables. None follows from the stated assumptions. Thus schurB cannot be applied directly.

### 4. BOTTOM LINE

- **YES:** the proposed bridge is a sound pointwise extended-real inequality, assuming `outerDom` is a product box and \(C_{\mathrm{resid}}\ge0\).
- **YES:** S4 is a real architectural obstruction to identifying the RHS with `ChargedRectSchurCore`.
- But it is **not the only issue**: the dropped upper bound may be infinite even when the original front integral is finite.