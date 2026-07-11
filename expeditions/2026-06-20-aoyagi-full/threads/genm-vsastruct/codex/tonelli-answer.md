The rank-drop tubes are rescued by codimension. They do not lower the critical exponent below \(7/2\). However, the full integral is not finite at the literal endpoint \(c'=7/2\): the generic sector slice already diverges logarithmically there.

### Q1 — \(U_1\)

**FACT.**
\[
\int_0^\varepsilon
U_1^{-(c'-2)}U_1^{4/2-1}\,dU_1
=
\int_0^\varepsilon U_1^{3-c'}\,dU_1.
\]
Hence
\[
3-c'>-1
\quad\Longleftrightarrow\quad
\boxed{c'<4}.
\]

At \(c'=7/2\), the exponent is \(-1/2\), so the normal integral converges. Since
\[
4>\frac72,
\]
the \(U_1=0\) stratum is non-binding.

Equivalently, in the four normal coordinates
\[
z=\bar vA_2\in\mathbb R^4,
\]
the singularity is
\[
\|z\|^{-s},\qquad s=2(c'-2),
\]
and
\[
\int_{\|z\|<\varepsilon}\|z\|^{-s}\,dz<\infty
\iff s<4
\iff c'<4.
\]

**INFERENCE.** This is precisely the requested Morse–Bott/norm-power codimension rescue.

### Q2 — \(U_0\) and \(A_2=0\)

**FACT.** For \(U_0\), using \(d_0=8\),
\[
\int_0^\varepsilon
U_0^{-(c'-3/2)}U_0^{8/2-1}\,dU_0
=
\int_0^\varepsilon U_0^{9/2-c'}\,dU_0.
\]
Thus
\[
\boxed{c'<\frac{11}{2}}.
\]
At \(c'=7/2\), the integrand is \(U_0^1\).

At \(A_2=0\), writing \(r=\|A_2\|\) in twelve dimensions,
\[
\int_0^\varepsilon r^{-2c'}r^{11}\,dr
=
\int_0^\varepsilon r^{11-2c'}\,dr,
\]
so
\[
\boxed{c'<6}.
\]
At \(c'=7/2\), this is \(\int r^4\,dr\).

Both \(11/2\) and \(6\) are strictly above \(7/2\). Neither stratum binds.

### Q3 — Correlation and rank \(2\)

**FACT.** The assertion that both units vanish on the entire rank-drop locus is false.

Let \(W=\operatorname{span}(w_1,w_2)\). The stated codimension \(8\) implies \(\dim W=2\).

- \(U_1=0\) means \(\bar vA_2=0\). Generic matrices here have rank \(2\); their left kernel is \(\mathbb R\bar v\).
- \(U_0=0\) means \(W\subseteq\ker(A_2^{\mathsf T})\), forcing \(\operatorname{rank}A_2\le1\).

Consequently, at a nonzero rank-\(2\) point, \(U_0>0\). Only the \(U_1\) singularity occurs there, with threshold \(c'<4\).

When \(\bar v\notin W\), use linear coordinates
\[
X=(w_1A_2,\delta w_2A_2)\in\mathbb R^8,\qquad
Z=a_{\rm piv}\bar vA_2\in\mathbb R^4.
\]
Then \(U_0\asymp\|X\|^2\), \(U_1\asymp\|Z\|^2\), and simultaneous vanishing means \(A_2=0\). Put \(R=\|X\|\), \(T=\|Z\|\). The deep measure is
\[
R^7T^3\,dR\,dT.
\]

The two correlated sectors give:

\[
\begin{array}{c|c|c}
\text{sector}&S&\text{conditions}\\ \hline
T\le R&R^{-4}T^{4-2c'}&c'<4,\ c'<6\\
R\le T&R^{3-2c'}T^{-3}&c'<11/2,\ c'<6
\end{array}
\]

Thus the strongest additional deep constraint is \(c'<4\), still strictly above \(7/2\). There is no hidden mixed or rank-\(2\) threshold.

If exceptionally \(\bar v\in W\), simultaneous vanishing occurs along \(U_0=0\), but the transverse space has dimension \(8\) and the homogeneous singularity is \(\|X\|^{-2c'}\). Its threshold is again
\[
2c'<8\iff c'<4.
\]
So even this correlation does not bind at \(7/2\).

**INFERENCE.** No separate deeper resolution is analytically required for finiteness in this concrete model, though a proof may still stratify the rank-drop tubes.

### Final verdict

For every
\[
\boxed{c'<7/2},
\]
the joint one-peel integral is finite, and the \(A_2\)-rank-drop divergence is rescued by codimension compensation. The critical exponent remains \(7/2\); no deeper rank-drop stratum lowers it.

Literally at \(c'=7/2\), however,
\[
S(U_0,U_1;7/2)=\infty
\]
for every \(U_0,U_1>0\), with radial behavior \(\int r^{-1}dr\). Hence Tonelli gives
\[
\boxed{\int S\,d\mu=\infty\quad\text{at }c'=7/2}.
\]
This endpoint divergence is the generic sector slice, not an \(A_2\)-rank-drop obstruction.