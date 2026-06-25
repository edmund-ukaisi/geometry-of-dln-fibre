**Verdict: WITNESS.**

**FACT:** At the deepest point, in identity-corner coordinates,
\[
C^{(s)}=\begin{pmatrix}I_r+X_s&Y_s\\ Z_s&T_s\end{pmatrix}.
\]
For \(L\ge 2\), the linearization of \(P=C^{(1)}\cdots C^{(L)}\) at this point is
\[
d(P-B)=
\begin{pmatrix}
\sum_s X_s & Y_L\\
Z_1 & 0
\end{pmatrix}.
\]

**INFERENCE:** The regular generators are exactly the output blocks
\[
P_{11}-I_r,\quad P_{12},\quad P_{21},
\]
with pivots
\[
X_1,\quad Y_L,\quad Z_1
\]
respectively. Their count is
\[
r^2+r(M^{L+1}-r)+(M^1-r)r
= r(M^1+M^{L+1})-r^2=nReg.
\]
So the relevant Jacobian minor is the identity, up to sign convention. This is an explicit unit-pivot witness, not an appeal to a constant-rank theorem.

**FACT:** The triangular solve can be written by block multiplication. If \(S=C^{(2)}\cdots C^{(L)}\), then \(S_{11}\) has constant term \(I_r\), hence is a unit, and
\[
P_{21}=Z_1S_{11}+T_1S_{21},\qquad
P_{11}=(I+X_1)S_{11}+Y_1S_{21}.
\]
These solve explicitly for \(Z_1\) and \(X_1\). Then using \(R=C^{(1)}\cdots C^{(L-1)}\), with \(R_{11}\) again a unit,
\[
P_{12}=R_{11}Y_L+R_{12}T_L
\]
solves explicitly for \(Y_L\).

**INFERENCE:** There is no hidden non-triangular obstruction for any \(r,M\) satisfying the deepest-point hypotheses \(r\le M^s\). Zero-size edge blocks simply delete the corresponding pivot family; full-rank cases have zero core. The identity-corner form always supplies the private unit pivots.

**Deepest Point:** Cleaner than the arbitrary fibre-point case. At the deepest point the rank-\(r\) identity corners are already present by construction, so no preliminary gauge or block-normalization step is needed.

**Core Caveat:** The RLCT split is obtained via explicit analytic/unit generator equivalence: after regular coordinates, the remaining bottom-right block is replaced by the Schur-complement/core generator, with only unit denominators. If one demanded literal Euclidean equality of the original squared norm after source coordinates only, that is stronger than needed and resembles Morse splitting. For `product_reduction`/RLCT, the explicit unit-pivot witness suffices.