**Q1.** The right mechanism is mixed: keep the collapsing \(\Gamma\)-directions in the bounded box, then recurse on the residual bilinear corner.

Exact for the 3-width rank-\((b-1)\) corner: on a chart with a rank-\((b-1)\) minor of \(Q_b\) invertible,
\[
Q_b \sim \begin{pmatrix} I_{b-1}&0\\0&z\end{pmatrix},
\qquad z\in\mathbb R^D,\quad D=q-b+1,
\]
and write \(\Gamma=(\Gamma_\parallel,\gamma)\), \(\gamma\in\mathbb R^a\). The \(\Gamma_\parallel\) directions are honest Morse directions and give charge \(a(b-1)\). What remains is the bounded-box bilinear model
\[
\|B_0\|^2+\|C'B_0+\gamma z\|^2 .
\]
The local zeta threshold of \(\gamma z\), with \(\gamma\in\mathbb R^a\), \(z\in\mathbb R^D\), is
\[
\frac12\min(a,D).
\]
Thus the corner has effective codimension
\[
tq+a(b-1)+\min(a,q-b+1)
\]
for a 3-width chain. Equivalently the bound is
\[
\int_{\Gamma,z}\mathrm{freed}^{-c'}\lesssim
\|B_0\|^{-2c' + a(b-1)+\min(a,D)}
\]
up to harmless logs. This reaches \(c'<\frac12\minAdm(M)\) because
\[
\minAdm(M)\le tq+a(b-1)+\min(a,D).
\]

For longer chains, the same statement should be read recursively: the missing singular row is not estimated by \(\det(Q_bQ_b^T)^{-a/2}\); it is a smaller zero-product problem involving the flat \(\Gamma\)-block and the deeper tail normal variables.

**Q2.** For 3 widths, \(Q_b\in\mathbb R^{b\times q}\), so
\[
D_{\mathrm{deep}}=\operatorname{codim}\{\operatorname{rank}Q_b\le b-1\}=q-b+1.
\]
The already-paid charge is
\[
tq+a(b-1).
\]
In the dangerous case \(a\ge D_{\mathrm{deep}}\),
\[
\minAdm(M)\le tq+a(b-1)+D_{\mathrm{deep}},
\]
which is exactly the candidate cut \(t+1\):
\[
(t+1)q+(a-1)(b-1)=tq+a(b-1)+q-b+1.
\]
Sharp form:
\[
\minAdm(M)\le tq+a(b-1)+\min(a,D_{\mathrm{deep}}).
\]

**Q3.** It is genuinely part of the same peel unless the global proof explicitly repartitions it after a further blow-up. Rank loss of \(Q_b\) is a tail condition, not an \(A_0\)-minor condition. Points with \(\Gamma=0\) and \(\operatorname{rank}Q_b<b\) need not lie in any \(t+1\) \(A_0\)-pivot chart. So a single \(t\)-peel cannot just prove the full-row-rank locus and ignore the complement. The exponent, however, is governed by the neighboring \(t+1\) admissible cut.