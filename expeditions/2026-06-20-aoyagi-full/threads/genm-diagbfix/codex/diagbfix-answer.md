### Q1

[FACT] Let the singular values of \(Z\) be \(s_1,s_2,s_3\asymp1\) and \(s_4=\sigma\to0\). Up to bounded linear distortions,
\[
\int_{\Omega_Z}\frac{dy}{\|y\|}
\asymp
\int_0^1 \rho^2\!\int_0^\sigma
\frac{ds}{\sqrt{\rho^2+s^2}}\,d\rho .
\]
Splitting at \(\rho=\sigma\),
\[
\int_0^\sigma(\cdots)d\rho=O(\sigma^3),\qquad
\int_\sigma^1 \rho^2\frac{\sigma}{\rho}\,d\rho
=\Theta(\sigma).
\]
Hence
\[
\int_{\Omega_Z}\|y\|^{-1}dy=\Theta(\sigma).
\]

[FACT] Since \(|\det Z|=\Theta(\sigma)\),
\[
J(Z)=|\det Z|^{-1}\Theta(\sigma)=\Theta(1).
\]
Indeed \(J(Z)\) tends to the finite rank-three integral
\[
\int_{[-1,1]^4}\|xZ_0\|^{-1}dx,
\]
whose singularity is \(\|v\|^{-1}\) in three transverse variables.

[INFERENCE] **VERDICT Q1:** \(J(Z)\) stays bounded; it does not blow up like \(|\det Z|^{-1}\).

### Q2

[FACT] Define
\[
L(Z):=\frac{J(Z)}{\det(ZZ^\top)^{-1/2}}
      =|\det Z|\,J(Z)
      =\int_{\Omega_Z}\|y\|^{-1}dy.
\]
Under \(Z=tZ_0\),
\[
L(tZ_0)
=\frac{|t|^{-1}J(Z_0)}{|t|^{-4}\det(Z_0Z_0^\top)^{-1/2}}
=|t|^3L(Z_0).
\]

[INFERENCE] Thus \(L(tZ_0)\to0\), so no local positive lower bound \(\inf L>0\) exists.

[INFERENCE] **VERDICT Q2:** The colleague’s proposed lower bound is false; the “fibre volume” collapses like \(t^3\).

### Q3

[FACT] A non-integrable upper bound proves nothing about divergence:
\[
0\le f\le g,\qquad \int g=+\infty
\]
is compatible with either \(\int f<\infty\) or \(\int f=\infty\).

[FACT] Here the thin image \(\Omega_Z\) supplies exactly the volume collapse omitted by replacing its integral with a \(Z\)-independent constant. Near rank three that collapse is \(\Theta(\sigma)\), canceling \(|\det Z|^{-1}=\Theta(\sigma^{-1})\).

[INFERENCE] **VERDICT Q3:** The determinant computation only makes the naive upper bound vacuous. It is not a divergence proof for \(I(q)\).

### Q4

[FACT] Write \(x=A_{\rm cor}\), \(d=P^{-1}B\), and
\[
V=A_0'+d\,x.
\]
Then
\[
Q_t=VZ,\qquad E_{\rm top}=\|PVZ\|_F^2.
\]
Near a fixed invertible \(P\), the loss is comparable from below to \(\|VZ\|_F^2\).

[FACT] At a rank-three \(Z_0\), let \(\ell\) span its left kernel and let \(r\) be the transverse singular-value coordinate. Decompose
\[
V_i=\alpha_i\ell+w_i,\qquad w_i\in\ell^\perp .
\]
There are \(3\times3=9\) coordinates in \(w\), and locally
\[
\|VZ\|_F^2\asymp \|w\|^2+r^2\|\alpha\|^2.
\]
For generic \(\alpha\ne0\), the nine \(w\)-directions plus the one deep direction \(r\) give
\[
C=10.
\]

[FACT] The charge has no negative \(r\)-exponent after integration in \(x\). Indeed, writing \(x=\beta\ell+\xi\), \(\xi\in\ell^\perp\simeq\mathbb R^3\),
\[
\|xZ\|^{-1}\asymp
\bigl(\|\xi\|^2+r^2\beta^2\bigr)^{-1/2},
\]
and
\[
\int_{\|\xi\|<1}
\bigl(\|\xi\|^2+r^2\beta^2\bigr)^{-1/2}d\xi=O(1).
\]

[FACT] Consequently the rank-drop channel has radial integral
\[
\int_0^\varepsilon \rho^{C-1-2q}\,d\rho
=\int_0^\varepsilon \rho^{9-2q}\,d\rho.
\]
It converges exactly when \(q<5\); for \(q=\tfrac12\) its exponent is \(8\).

[FACT] Finiteness at \(q=\tfrac12\) also follows globally without relying on this local model. Put
\[
R=\begin{bmatrix}A_0'\\x\end{bmatrix},\quad S=RZ,\quad M=[\,P\ B\,].
\]
Since \(E_{\rm tr}\ge0\),
\[
\text{integrand}\le \|xZ\|^{-1}\|MS\|_F^{-1}.
\]
For fixed \(S\),
\[
\int_{M\text{-box}}\|MS\|_F^{-1}dM
\le \frac{C}{\|S\|_F}
\le \frac{C}{\|xZ\|}.
\]
Therefore it suffices to integrate \(\|xZ\|^{-2}\). For fixed \(x\), the four column projections of \(Z\) give
\[
\int_{Z\text{-box}}\|xZ\|^{-2}dZ\le C\|x\|^{-2},
\]
and
\[
\int_{\|x\|<1}\|x\|^{-2}dx
\asymp\int_0^1 r^{4-1-2}dr<\infty.
\]

[INFERENCE] **VERDICT Q4:** \(I(\tfrac12)<\infty\). The rank-three deep drop has effective codimension \(C=10\), not a codimension-one \(|\det Z|^{-1}\) pole.

[INFERENCE] **FINAL VERDICT:** The disputed claim is **FALSE**. The sharpest reason is the explicit finite estimate \(I(\tfrac12)<\infty\); geometrically, the thin fibre volume cancels the apparent determinant pole.