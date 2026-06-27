The adjudication is: **\(\Psi\) does not generically preserve \(P_{11}\)**. The numeric \(E2\) preservation must come from the framed endpoint map not leaking the changed \((2,2)\) block into the three read blocks.

For the raw block:
\[
\Delta P_{11}
= Z_0(Y_1'-Y_1)+T_0(T_1'-T_1)
= Z_0A_0^{-1}Y_0(T_1-T_1')+T_0(T_1'-T_1)
\]
\[
= (Z_0A_0^{-1}Y_0-T_0)(T_1-T_1')
= -S_0(T_1-T_1')
= S_0(T_1'-T_1).
\]
So the exact zero condition is
\[
S_0(T_1'-T_1)=0.
\]
The sufficient special cases \(S_0=0\) or \(T_1'=T_1\) make it vanish, but \(\Psi\) does **not** impose this identity in general. Thus the raw flat product is not wholly fixed.

Now let
\[
U=\begin{pmatrix}u_{11}&u_{12}\\u_{21}&u_{22}\end{pmatrix},
\qquad
V=\begin{pmatrix}v_{11}&v_{12}\\v_{21}&v_{22}\end{pmatrix},
\qquad
\Delta P=\begin{pmatrix}0&0\\0&D\end{pmatrix}.
\]
Then
\[
U\Delta P V
=
\begin{pmatrix}
u_{12}Dv_{21} & u_{12}Dv_{22}\\
u_{22}Dv_{21} & u_{22}Dv_{22}
\end{pmatrix}.
\]
The framed read blocks \((1,1),(1,2),(2,1)\) are independent of \(P_{11}\) exactly when
\[
u_{12}Dv_{21}=0,\qquad
u_{12}Dv_{22}=0,\qquad
u_{22}Dv_{21}=0
\]
for the relevant \(D\), or as identities for all possible \((2,2)\)-block changes \(D\).

In the usual nondegenerate/invertible endpoint situation, this reduces to
\[
u_{12}=0,\qquad v_{21}=0.
\]
So \(U=\) `endpointP0` is **block lower triangular** in the \(r\oplus(\cdot-r)\) order, and \(V=\) `endpointQL` is **block upper triangular**. With that structure, the only possible effect of \(\Delta P_{11}\) lands in the output \((2,2)\) block, which the energy does not read.