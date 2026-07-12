### Q1 — VERDICT: holds after reshape, but not literally

**Re-derived.** Write
\[
A=A_3,\quad r=A_{2,\mathrm{cor}},\quad
G_0=P A_{2,\mathrm{top}}+B_{12}r,\quad h=CP^{-1},\quad q=rA.
\]
Then
\[
\mathrm{Base}
=\|G_0A\|_F^2+\|hG_0A(I-P_q)\|_F^2.
\]

It is not literally a γ′-loss in the original coordinates. For example, with the specialization described above,
\[
\mathrm{Base}=\|A\|_F^2+\frac{(xt-yz)^2}{z^2+t^2}.
\]
For tail-independent \(G'\), \(\|G'A\|_F^2\) is polynomial and quadratic in \(A\); this expression is genuinely rational and has direction-dependent behaviour as \((z,t)\to0\). Arbitrary rational carrier coefficients do not help because the γ′ clause fixes the residuals to the entries of \(G'A\).

Nevertheless, on the Gram-nondegenerate chart \(q\neq0\), there is a genuine tail-dependent change of active coordinates that removes the projection.

Choose orthonormal bases \((m,n)\) and \((\ell,k)\) with
\[
m=q^\top/\|q\|,\qquad \ell=r^\top/\|r\|,
\]
and \(n,k\) their perpendicular vectors. Then
\[
Am=\alpha\ell+\beta k,\qquad An=\delta k,\qquad
\alpha=\frac{\|q\|}{\|r\|}>0.
\]
Let \(S_h=(I+h^\top h)^{1/2}\), and define \(G'\) by
\[
G'k=S_hG_0k,\qquad
G'\ell=G_0\ell+\frac{\beta}{\alpha}(I-S_h)G_0k.
\]
This is an invertible linear change \(G_0\mapsto G'\) for fixed spectators, and a direct calculation gives
\[
\boxed{\mathrm{Base}=\|G'A\|_F^2.}
\]
The tied tail remains exactly \(A=A_3\), and the entries of \(G'\) are free active coordinates. Hence, at the **loss level**, this is a legitimate γ′-form reshape on \(q\neq0\).

**Inference.** This reshape is an additional CoV, not an output of the stated peel. Its active-coordinate Jacobian is
\[
\det S_h=\sqrt{1+\|h\|^2},
\]
so an exact equality of decorated integrals also requires handling this spectator-dependent density and the transformed domain. It is bounded on the usual compact pivot chart, but it is not itself an exceptional-coordinate monomial. No single such chart extends through \(q=0\).

### Q2 — VERDICT: does not hold at the reduced-IH handoff

**Re-derived.** Here
\[
g=\det(Q_bQ_b^\top)=\|q\|^2.
\]
Holding the existing exceptional coordinates \(u\) fixed, \(g^{-1/2}\) varies with the tied tail. It therefore cannot equal a monomial \(\prod |u_\ell|^{j_\ell}\). Relabelling variables or using arbitrary carrier coefficients cannot change that measure-theoretic fact.

It can become monomial only after another sector decomposition or resolution. For example, if \(q=(z,t)\), on a chart \(t=zv\),
\[
(z^2+t^2)^{-1/2}
=|z|^{-1}(1+v^2)^{-1/2}.
\]
The singular part is then monomial in the new exceptional coordinate \(z\), while the remaining factor is a smooth unit. Producing this chart and its Jacobian is a further CoV, not part of the peel.

On the units sector \(g\ge c>0\), let \(e=c'-\tfrac12>0\). Then
\[
g^{-1/2}\mathrm{Base}^{-e}
\le c^{-1/2}w^{-e}.
\]
Moreover,
\[
w=\|G_0A_3\|_F^2,
\]
so the comparator loss is literally γ′-form with tied tail \(A_3\); \(A_{2,\mathrm{top}}\mapsto G_0\) is invertible because \(P\) is invertible. Thus, assuming the other inherited admissibility clauses, the **comparator decoration** can satisfy `adm`.

But domination does not make the Base-decoration admissible. The correct IH pattern is:

1. construct an actually admissible decoration with loss \(w\);
2. apply the IH to it;
3. use the external pointwise integral comparison.

Calling the IH directly on a decoration whose loss is `Base`, or whose jacobian weight contains \(g^{-1/2}\), is not justified.

The most likely way this verdict is wrong is if the formal meaning of “legitimate reshape” forbids tail-dependent active-coordinate changes or requires exact preservation of the standard measure. In that case Q1 must be downgraded to “does not hold”; its literal-failure conclusion and Q2 remain unchanged.