The natural fixed-coordinate answer is: no single gauge. The full Case-1 chart family needs pivot-dependent gauges, and the \(u\)-pivot chart is the decisive obstruction.

1. The \(u\)-pivot does not use the d-entry Schur gauge

In the \(u\)-pivot chart,
\[
D=uD'.
\]
No entry of \(D'\) is normalized to \(1\); it may even be the zero matrix. Hence there is no regular matrix pivot on which to perform Schur elimination. Aoyagi’s Case 1(1) only absorbs \(u\) into the monomial data and recurses. It does not introduce the \(Q/P\) clearing of Case 1(2).

Thus, in the natural coordinates,
\[
\psi_u=\mathrm{id}
\]
up to harmless relabelling, whereas for a d-entry pivot \(p=(r,c)\),
\[
(\psi_p D)_{ij}=d_{ij}-d_{ic}d_{rj},
\qquad i\ne r,\ j\ne c,
\]
in the normalized pivot frame. This is nontrivial generically.

For example, at the corner pivot,
\[
\begin{pmatrix}1&a\\ b&c\end{pmatrix}
\longmapsto c-ba
\]
on the complementary entry. Taking \(a=b=\tfrac12,c=0\) distinguishes this gauge from the identity.

The \(u\)-chart also cannot be discarded as a “ledger-only extra”: it is the unique standard chart covering the \(u\)-axis direction
\[
D=0,\qquad u\ne0.
\]
Every d-pivot chart has pivot \(d_{rc}=0\) there and therefore sends all center coordinates to zero.

So, with pure standard \(\beta_p\) in one fixed ambient frame,
\[
\operatorname{chartMap}_p=\psi\circ\beta_p
\]
cannot hold with one \(p\)-independent \(\psi\).

2. Different gauges do not automatically preserve the pure-pivot cover

Put \(S_p=\beta_p(D_p)\). In general,
\[
\bigcup_p\psi_p(S_p)
\ne
\psi\!\left(\bigcup_pS_p\right)
\]
for any geometrically meaningful common \(\psi\).

Indeed, independently shearing covering sectors can create gaps. In \(\mathbb R^2\), let
\[
C_1=\{|y|\le |x|\},\qquad C_2=\{|x|\le |y|\},
\]
so \(C_1\cup C_2=\mathbb R^2\). Take
\[
\psi_1=\mathrm{id},\qquad \psi_2(x,y)=(x+y^2,y).
\]
This is a polynomial determinant-one homeomorphism tangent to the identity. For \(0<t<1\),
\[
z_t=(-t+t^2/2,t)
\]
lies neither in \(C_1\) nor in \(\psi_2(C_2)\). Hence the sheared family misses points arbitrarily close to the origin.

The actual cleaned blow-up atlas nevertheless covers when the clearing is treated correctly as a chart-coordinate change. If \(\alpha_p\) is the cleaning automorphism of the \(p\)-th source chart, then
\[
\widetilde\beta_p=\beta_p\circ\alpha_p^{-1},
\qquad
\widetilde\beta_p(\alpha_p(D_p))=\beta_p(D_p).
\]
Thus the chart image is unchanged after adapting the domain.

If the formalisation insists on target-postcomposition \(\psi_p\circ\beta_p\), the correct node statement is instead
\[
Z_{\mathrm{node}}\cap B
\subset U
\subset
\bigcup_p(\psi_p\circ\beta_p)(D_p),
\]
with \(U\) open. One sufficient per-edge formulation chooses open \(V_p\) such that
\[
Z_{\mathrm{node}}\cap B\subset\bigcup_pV_p,
\qquad
\psi_p^{-1}(V_p)\subset\beta_p(D_p).
\]

Merely knowing every \(\psi_p\) is a determinant-one homeomorphism is insufficient.

Literally, every union is \(\mathrm{id}''(\text{that union})\); that tautology is not the factorization needed by the shared-gauge lemma.

3. The d-entry gauges are themselves pivot-dependent

In fixed matrix coordinates, different pivots modify different complementary entries. For a \(2\times2\) block:

- pivot \((1,1)\) updates \(x_{22}\mapsto x_{22}-x_{21}x_{12}\);
- pivot \((1,2)\) updates \(x_{21}\mapsto x_{21}-x_{22}x_{11}\).

They are not the same ambient map.

If \(\sigma_p\) moves pivot \(p\) to the corner, “the same formula in the post-pivot frame” means
\[
\psi_p=\sigma_p^{-1}\psi_0\sigma_p.
\]
That proves conjugacy, not equality. It yields a common ambient \(\psi\) only if these conjugates agree—equivalently, \(\psi_0\) commutes with every pivot-changing transition—or if the chart definitions absorb the frames so completely that one proves
\[
\psi_p\circ\beta_p=\psi\circ\widetilde\beta_p
\]
and separately proves that the \(\widetilde\beta_p\)-images still give the pure-pivot cover.

“Same syntax after renaming indices” is not enough. On overlaps, the induced restrictions must actually agree.

4. Lean-design verdict

For pure \(\beta_p\) in one common coordinate frame, the single-per-node-gauge lemma is not sufficient for a Case-1 node. A per-edge-gauge cover—or a source-reparameterization theorem preserving each chart image—is required.

The deciding check is the literal hypothesis
\[
\exists\psi\;\forall p,w\in D_p,\quad
\operatorname{localSub}_p(w)=\psi(\beta_p(w)),
\]
including the \(u\)-pivot and at least two distinct d-entry pivots. The \(u\)-identity versus d-Schur comparison already makes this fail in the natural Aoyagi model.

A shared-gauge lemma remains usable only after a deliberate modelling change that absorbs all pivot frames and clearing differences into the \(\beta_p\) or applies a genuinely common gauge to every chart. That change must re-establish both the pure-pivot image cover and the pullback identities; determinant \(1\) does not decide either issue.