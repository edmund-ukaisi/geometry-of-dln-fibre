**Derived Construction**

Let
\[
r_s=t_{s-1}-t_s,\qquad c_s=M_s-t_s,\qquad d_s=r_sc_s,\qquad D=\sum_{s=1}^L d_s=\operatorname{minAdm}(M).
\]
Use block coordinates with the kept \(t_s\) coordinates first.

For each \(1\le s<L\), choose
\[
X_s\in \mathbb R^{r_s\times t_s},\quad N_s\in \mathbb R^{t_s\times c_s},
\]
and an invertible-core chart
\[
K_s=\mathcal L_s\operatorname{diag}(q_{s,1},\dots,q_{s,t_s})\mathcal U_s,
\]
where \(\mathcal L_s,\mathcal U_s\) are unit lower/upper triangular. Define
\[
P_s=\begin{bmatrix}I_{t_s}\\ X_s\end{bmatrix},\qquad
Q_s=\begin{bmatrix}I_{t_s}&N_s\end{bmatrix}.
\]

Pick one residual slot in a positive \(d_s\)-block and set its coefficient equal to \(1\); all other residual coefficients are free. For strict paths with \(M_L>0\), take this slot in the final block \(s=L\). Write the resulting coefficient blocks as \(R_s\), with exactly one fixed entry among all \(R_s\)’s.

For \(1\le s<L\), define the compressed transition
\[
C_s
=
P_sK_sQ_s
+
u\begin{bmatrix}
0&0\\
0&R_s
\end{bmatrix}
=
\begin{bmatrix}
K_s&K_sN_s\\
X_sK_s&X_sK_sN_s+uR_s
\end{bmatrix}.
\]
For the final boundary,
\[
C_L=uR_L\in \mathbb R^{t_{L-1}\times M_L}.
\]

Now chain these compressed transitions into the actual factors. Define
\[
G_s=\begin{bmatrix}I_{t_s}&N_s\\0&I_{c_s}\end{bmatrix},
\qquad 1\le s<L.
\]
Let \(W_{s+1}\in\mathbb R^{c_s\times M_{s+1}}\) be free lift variables. Then
\[
A^{(0)}=C_1,
\]
and for \(1\le s<L\),
\[
A^{(s)}
=
G_s^{-1}
\begin{bmatrix}
C_{s+1}\\
W_{s+1}
\end{bmatrix}
=
\begin{bmatrix}
C_{s+1}-N_sW_{s+1}\\
W_{s+1}
\end{bmatrix}.
\]
Equivalently,
\[
Q_sA^{(s)}=C_{s+1}.
\]
This is the uniform \(B/C\)-style chaining. In your \((3,3,3,3)\) chart, this gives exactly
\[
B=\begin{bmatrix}D-mr\\ r\end{bmatrix},\qquad
C=\begin{bmatrix}u\zeta-n_1h_1-n_2h_2\\ h_1\\ h_2\end{bmatrix}.
\]

**Exact Telescoping**

Let
\[
S_s=C_sA^{(s)}A^{(s+1)}\cdots A^{(L-1)}.
\]
Then \(S_L=C_L=uR_L\). For \(s<L\),
\[
S_s
=
(P_sK_sQ_s+u\bar R_s)A^{(s)}\cdots A^{(L-1)}
=
P_sK_sS_{s+1}
+
u\bar R_sA^{(s)}\cdots A^{(L-1)}.
\]
By backward induction, every \(S_s\) is divisible by \(u\). Hence
\[
A^{(0)}A^{(1)}\cdots A^{(L-1)}=uH
\]
as an exact polynomial identity. Therefore
\[
F(\Phi(u))=u^2\|H\|_F^2=u^2V.
\]

At the sector point
\[
q_{s,i}=1,\quad \mathcal L_s=\mathcal U_s=I,\quad X_s=N_s=W_s=0,
\]
all free residuals \(0\), and the distinguished final residual entry \(R_L(1,1)=1\), we get \(H|_{u=0}=E_{11}\). Thus
\[
V|_{u=0}\not\equiv 0,
\]
and on a small positive-measure box around this point,
\[
0<c_0<V<B.
\]
So the minimum \(u\)-degree of \(F\) is exactly \(2\).

**Jacobian**

For the unscaled local Schur map
\[
(X,K,N,E)\mapsto
\begin{bmatrix}
K&KN\\
XK&XKN+E
\end{bmatrix},
\]
the exact Jacobian is
\[
|\det K|^{r_s+c_s}.
\]
For the LDU core chart,
\[
K_s=\mathcal L_s\operatorname{diag}(q_{s,1},\dots,q_{s,t_s})\mathcal U_s,
\]
the exact Jacobian is
\[
\prod_{i=1}^{t_s}|q_{s,i}|^{2(t_s-i)}.
\]
The chaining map
\[
(C_{s+1},W_{s+1})\mapsto A^{(s)}
\]
has determinant \(1\), since \(G_s\) is unit triangular.

The common radial residual substitution gives
\[
(y_\ast,y_j)=(u,u\rho_j),
\]
so its Jacobian is exactly
\[
|u|^{D-1}.
\]

Hence
\[
\boxed{
|\det D\Phi|
=
|u|^{\operatorname{minAdm}(M)-1}
\prod_{s=1}^{L-1}
\prod_{i=1}^{t_s}
|q_{s,i}|^{\,r_s+c_s+2(t_s-i)}
}.
\]
For \((3,3,3,3)\), this gives
\[
|u|^5|a|^4|\delta|^2|b|^3.
\]

Thus the binding axis has
\[
(k_u,h_u)=(1,\operatorname{minAdm}(M)-1),
\]
and all pivot variables are \(k=0\) spectators. The threshold is
\[
\frac{\operatorname{minAdm}(M)-1+1}{2}
=
\frac{\operatorname{minAdm}(M)}2.
\]

**Codimension-Zero Boundaries**

If \(d_s=0\), nothing singular happens.

If \(r_s=0\), rank stays:
\[
C_s=K_s\begin{bmatrix}I&N_s\end{bmatrix}.
\]
No residual block appears.

If \(c_s=0\), width equals kept rank:
\[
C_s=\begin{bmatrix}I\\X_s\end{bmatrix}K_s,
\qquad Q_s=I.
\]
Then the next chaining lift has no lower rows, so the factor simply passes through.

If both vanish, \(C_s=K_s\). These cases contribute only the spectator pivot monomial above, never a \(u\)-power.

Everything above is derived algebraically. The only terminology correction is that \(\Phi\) is a polynomial chart that is a diffeomorphism on the sector \(u\ne0\), \(q_{s,i}\ne0\); it necessarily has vanishing Jacobian on \(u=0\).