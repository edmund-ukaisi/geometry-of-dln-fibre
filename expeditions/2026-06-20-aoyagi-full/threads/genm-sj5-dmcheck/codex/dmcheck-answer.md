## Q1 — NO

At a generic point of a binding product-rank component, \(m=1\).

For a concrete higher-corank test, take
\[
M=(4,3,3,3),\qquad P=BC,\quad B,C\in\operatorname{Mat}_{3\times3}.
\]
The branch
\[
T=\{\operatorname{rank}B=1,\ \operatorname{rank}C=2,\ BC=0\}
\]
has dimension \(5+6=11\) in an \(18\)-dimensional space, hence codimension \(D=7\). It is binding since
\[
(D(\rho)+4\rho)_{\rho=0}^3=(7,7,9,12).
\]

At the generic point
\[
B_0=\operatorname{diag}(1,0,0),\qquad
C_0=\operatorname{diag}(0,1,1),
\]
a transverse slice gives
\[
B(t)C(t)
=t\begin{pmatrix}
x&y&z\\
0&a&b\\
0&c&d
\end{pmatrix}.
\]
For generic transverse direction \(x(ad-bc)\neq0\), this coefficient has rank \(3\). Therefore
\[
\sigma_{\min}(B(t)C(t))^2
=t^2\sigma_{\min}(L)^2,
\]
so \(m=1\), not \(m>1\).

This is the general product mechanism: a generic maximal rank-profile component is saturated, and its transverse first-order compression space contains matrices of the full missing rank \(q\). Higher order occurs only on nested angular loci where that first-order matrix drops rank. Those are descendant rank-profile tubes, not the generic tube.

Two cautions:

- \(\sigma_{\min}^2\) is not a polynomial “Gram minor”.
- \(\det(PP^{T})\sim t^{2q}\), but that is the product of all \(q\) collapsing singular values squared. Treating its order \(q\) as the order of \(\sigma_{\min}^2\) misreads \(m\).

Radicality of the target determinantal ideal alone is insufficient—radical ideals can acquire multiplicity under arbitrary pullback. What saves matrix products is the explicit reduced, full-rank first-order normal slice above.

## Q2 — YES, literally, but only for a nonbinding cell

The unqualified per-cell formula \((D_q+d_q)/2\) is false.

Take
\[
M=(1,5,3,3),\qquad G=wBC,
\]
with \(w\in\operatorname{Mat}_{1\times5}\), \(B\in\operatorname{Mat}_{5\times3}\), and \(C\in\operatorname{Mat}_{3\times3}\). The deeper product has \(r=3\). On the \(q=3\), \(\rho=0\) component
\[
T=\{C=0,\ \operatorname{rank}B=3\},
\]
we have
\[
D_3=\operatorname{cCodim}(BC;0)=\minAdm(5,3,3)=9,\qquad d_3=0.
\]
Thus the claimed value is \(9/2\).

Choose \(w_0B_0\neq0\). At \(C=0\),
\[
dG(\delta C)=w_0B_0\,\delta C:
\operatorname{Mat}_{3\times3}\longrightarrow\mathbb R^3
\]
is surjective. Hence \(G\) is locally a submersion onto three coordinates and
\[
\operatorname{RLCT}_{\mathrm{loc}}\|G\|^2=\frac32<\frac92.
\]

This is precisely
\[
\frac12\min(M_0q,D_q)=\frac12\min(3,9)=\frac32.
\]
But the cell is nonbinding:
\[
\minAdm(1,5,3,3)=3,
\]
so \(3/2\) is exactly the global RLCT, not an undershoot.

Thus the inequality in the prompt is reversed. To retain the tube contribution \(D\), one needs
\[
D/m\le n_0,
\]
not \(D/m\ge n_0\). The latter makes the minimum choose \(n_0\).

Also, every proposed example in the question has deeper generic rank \(2\), so none can test \(q\ge3\). Their \(D+d\) tables are:
\[
\begin{array}{c|c}
M & (D(\rho)+M_0\rho)_{\rho=0}^{2}\\ \hline
(5,2,5)&(10,9,10)\\
(2,5,2,2,5)&(4,3,4)\\
(7,2,2,2,7)&(3,8,14).
\end{array}
\]

## Q3 — NO

With the stated geometric definition,
\[
\min_{\rho}\bigl(D(\rho)+M_0\rho\bigr)=\minAdm(M)
\]
always.

Indeed, stratify the zero fibre \(A_0P=0\) by \(\operatorname{rank}P=\rho\). For fixed \(P\), the condition that \(A_0\) annihilate \(\operatorname{im}P\) imposes exactly \(M_0\rho\) independent equations. Therefore that stratum has codimension
\[
D(\rho)+M_0\rho,
\]
and taking the largest-dimensional stratum gives the identity.

A bottleneck can make the parameter-space codimension much smaller than the naïve target-matrix codimension, but this is already included in \(\operatorname{cCodim}\). For example, for \(P=BC\) with widths \((4,2,4)\),
\[
\operatorname{codim}\{BC=0\}=7,
\]
not the target-space value \(16\). The maximal branch has
\[
\operatorname{rank}B=\operatorname{rank}C=1,\qquad
\operatorname{im}C=\ker B.
\]
Its dimension is \(5+5-1=9\) in dimension \(16\), hence codimension \(7=\minAdm(4,2,4)\).

Scheme multiplicity or a singular pushforward density cannot lower this parameter-space Lebesgue codimension.

## Q4 — NO

No binding branch has threshold below \(\frac12\minAdm(M)\).

Let
\[
E(\rho)=D(\rho)+M_0\rho,\qquad q=r-\rho.
\]
If \(\rho\) is binding, comparison with the full-rank cell gives
\[
E(\rho)\le E(r)=M_0r
\quad\Longrightarrow\quad
D(\rho)\le M_0q.
\]
Since the generic transverse order is \(m=1\), the coupled corner gives
\[
\frac{M_0\rho}{2}
+\frac12\min\!\bigl(M_0q,D(\rho)\bigr)
=\frac{M_0\rho+D(\rho)}2.
\]
More generally, comparison with every intermediate rank \(t>\rho\) gives
\[
D(\rho)-D(t)\le M_0(t-\rho),
\]
which is exactly the charge inequality needed at each iterated corner.

Higher-order rays lie in nested rank-drop strata; nonbinding MIN corners merely reproduce another \(E(t)/2\), never something below \(\frac12\min_tE(t)\).

**NO COLLAPSE: generic binding product-rank tubes have \(m=1\), and binding forces \(D_q\le M_0q\), so the corner retains the full tube codimension.**