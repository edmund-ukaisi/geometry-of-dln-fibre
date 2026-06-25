**1. Verdict: verify.**  
Exact algebra:
\[
C_0C_1=
\begin{pmatrix}
(1+X_0)(1+X_1)+Y_0Z_1 & (1+X_0)Y_1+Y_0T_1\\
Z_0(1+X_1)+T_0Z_1 & Z_0Y_1+T_0T_1
\end{pmatrix}.
\]
On line A,
\[
C_0=\begin{pmatrix}1&Y_0\\0&0\end{pmatrix},\quad
C_1=\begin{pmatrix}1&-T_1Y_0\\0&T_1\end{pmatrix},
\]
so
\[
C_0C_1=\begin{pmatrix}1&-T_1Y_0+Y_0T_1\\0&0\end{pmatrix}
=\begin{pmatrix}1&0\\0&0\end{pmatrix}.
\]
Thus `dlnLoss = 0`. But with \(T_0=T_1=0\) imposed only inside \(P_r\),
\[
P_r=\begin{pmatrix}1&-T_1Y_0\\0&0\end{pmatrix},
\]
so
\[
E_{\rm reg}=(T_1Y_0)^2,\qquad \mathrm{core}\Phi=(T_0T_1)^2=0.
\]
Hence \(\Phi=(T_1Y_0)^2>0\) when \(Y_0T_1\neq 0\).

**2. Verdict: refute.**  
Exact algebra plus topology: no lower bound \(c_1\Phi\le dlnLoss\) can hold on any open ambient neighborhood of the deepest point. Every such neighborhood contains points of line A with \(Y_0,T_1\neq 0\), and there
\[
c_1\Phi=c_1(T_1Y_0)^2>0,\qquad dlnLoss=0.
\]
So the lower squeeze fails for every \(c_1>0\).

There is also a dual leak showing the upper bound fails for the same candidate \(\Phi\): take \(X_0=X_1=Z_0=Z_1=T_0=Y_1=0\), with \(Y_0,T_1\neq0\). Then \(\Phi=0\), but the full product has \(P_{12}=Y_0T_1\), so \(dlnLoss=(Y_0T_1)^2>0\).

**3. Verdict: verify for raw layer coordinates, refute for gauge-transversal coordinates.**  
Gauge-geometry inference: as entries of the two matrices, \(X_0,Y_0,Z_0,T_0,X_1,Y_1,Z_1,T_1\) are independent affine local coordinates. There is no hidden algebraic constraint excluding line A from the ambient parameter space.

But \(Y_0\) is not a genuine regular transverse coordinate. With the product-preserving gauge action
\[
(C_0,C_1)\mapsto (C_0G,G^{-1}C_1),
\]
the infinitesimal action at \(P=\operatorname{diag}(1,0)\), for
\[
G=I+\epsilon\begin{pmatrix}\alpha&\beta\\ \gamma&\delta\end{pmatrix},
\]
gives
\[
\delta C_0=P A=\begin{pmatrix}\alpha&\beta\\0&0\end{pmatrix},\qquad
\delta C_1=-A P=\begin{pmatrix}-\alpha&0\\-\gamma&0\end{pmatrix}.
\]
So the vertical gauge directions include \(X_0-X_1\), \(Y_0\), and \(Z_1\). The first-order product-transverse regular directions are instead
\[
X_0+X_1,\qquad Y_1,\qquad Z_0,
\]
or, nonlinearly, the full product blocks \(P_{11}-1,P_{12},P_{21}\).

Indeed line A is gauge-removable. For \(y=Y_0,t=T_1\), take
\[
G=\begin{pmatrix}1&-y\\0&1\end{pmatrix}.
\]
Then
\[
C_0G=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
G^{-1}C_1=\begin{pmatrix}1&0\\0&t\end{pmatrix}.
\]
So if the chart is a true gauge slice imposing \(Y_0=0\), line A with \(Y_0\neq0\) is not in that slice. But then the statement “all eight are independent transversal coordinates” is wrong. If the theorem quantifies over the ambient eight-coordinate chart, line A is reachable and the squeeze is false.

**4. Verdict: verify: the regular energy must use the full product, and the core should be product-invariant.**  
Exact algebra: write
\[
A=P_{11},\quad B=P_{12},\quad C=P_{21},\quad D=P_{22}.
\]
Then
\[
dlnLoss=(A-1)^2+B^2+C^2+D^2.
\]
The tautologically correct squeeze is therefore equality with
\[
\Phi_{\rm full}=(A-1)^2+B^2+C^2+D^2.
\]

For rank-chart geometry, the better normal-form core is the Schur complement
\[
S=D-CA^{-1}B,
\]
with \(A\) near \(1\). Then
\[
\Phi_{\rm Schur}=(A-1)^2+B^2+C^2+S^2
\]
is two-sidedly comparable to \(dlnLoss\) near the deepest point, because \(D=S+CA^{-1}B\), and \(CA^{-1}B\) is quadratic in the already-controlled regular blocks \(B,C\).

In layer coordinates, the invariant reduced core is not raw \(T_0T_1\) unless a gauge has pinned the off-diagonal spectators. With \(a_s=1+X_s\),
\[
\sigma_0=T_0-\frac{Z_0Y_0}{a_0},\qquad
\sigma_1=T_1-\frac{Z_1Y_1}{a_1},
\]
and in the scalar \(1\oplus1\) case,
\[
S=\frac{a_0a_1}{A}\,\sigma_0\sigma_1.
\]
In a slice such as \(Y_0=0,\ Z_1=0\), this reduces to \(S=T_0T_1\) up to the harmless unit factor. Outside such a slice, raw \(T_0T_1\) is not the invariant core.

OPTION-2 (weaken to comparability Sreg≍Ereg) is **UNSOUND** because the \(T=0\) regular energy is not comparable to the full-product regular energy: line A has full regular energy \(0\) but \(E_{\rm reg}>0\), and the uncancelled leak path has \(E_{\rm reg}=0\) but full regular energy \(>0\). The real fix is to use the full product regular blocks and an invariant core, either \(P_{22}\) for exact loss equality or the Schur complement for the rank-chart normal form.