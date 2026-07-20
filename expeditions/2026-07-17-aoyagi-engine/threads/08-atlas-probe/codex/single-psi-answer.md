I relabel the normalized \((J+1,J+1)\) pivot as index \(1\), so \(d'_{11}=1\), and write \(b_1=b'_{J+1}\).

## Q1. Explicit changes of variables

### \(2\times2\)

Write
\[
D'=\begin{pmatrix}1&x\\ y&z\end{pmatrix},
\qquad
B=\operatorname{diag}(b_1,b_2),
\qquad
\rho=\frac{b_2}{b_1}.
\]

**COMPUTE.**
\[
Q=\begin{pmatrix}1&-x\\0&1\end{pmatrix},
\qquad
Q^{-1}=\begin{pmatrix}1&x\\0&1\end{pmatrix},
\]
and
\[
D''=D'Q
 =\begin{pmatrix}1&0\\y&z-yx\end{pmatrix}.
\]
Thus \(d''_{21}=y\), and
\[
P=\begin{pmatrix}1&0\\-\rho y&1\end{pmatrix}.
\]
Indeed, putting \(w=z-yx\),
\[
PBD''
=
\begin{pmatrix}b_1&0\\0&b_2w\end{pmatrix}
=
B\begin{pmatrix}1&0\\0&w\end{pmatrix}.
\]

If the rows of the next-layer matrix are \(c_1,c_2\), then
\[
Q^{-1}C=
\begin{pmatrix}c_1+xc_2\\c_2\end{pmatrix}.
\]

Hence the square coordinate change on the retained chart coordinates is
\[
(x,y,z,c_1,c_2)
\longmapsto
\bigl(x,y,w=z-yx,\ \widetilde c_1=c_1+xc_2,\ \widetilde c_2=c_2\bigr).
\]

For one scalar column of \(C\), order the variables as
\[
(x,y,c_2,z,c_1).
\]
Its Jacobian is
\[
J_\Psi=
\begin{pmatrix}
1&0&0&0&0\\
0&1&0&0&0\\
0&0&1&0&0\\
-y&-x&0&1&0\\
c_2&0&x&0&1
\end{pmatrix},
\qquad
\det J_\Psi=1.
\]
Generically \(\operatorname{rank}(J_\Psi-I)=2\), so this is not one elementary transvection, although it is unit triangular.

For comparison, forcibly multiplying the two index-space matrices gives
\[
PQ=
\begin{pmatrix}
1&-x\\
-\rho y&1+\rho xy
\end{pmatrix},
\qquad
\det(PQ)=1.
\]
Moreover
\[
\chi_{PQ}(\lambda)
=\lambda^2-(2+\rho xy)\lambda+1,
\]
so \(PQ\) is generically not unipotent and
\[
\det(PQ-I)=-\rho xy\neq0
\]
generically. Thus it cannot be \(I+\) rank-one nilpotent.

However, \(PQ\) is not the faithful combined action: the actual operation is two-sided,
\[
A\longmapsto P A Q,
\]
together with \(C\mapsto Q^{-1}C\). For fixed parameters,
\[
\operatorname{vec}(PAQ)=(Q^{\mathsf T}\otimes P)\operatorname{vec}(A),
\]
where
\[
Q^{\mathsf T}\otimes P=
\begin{pmatrix}
1&0&0&0\\
-\rho y&1&0&0\\
-x&0&1&0\\
\rho xy&-x&-\rho y&1
\end{pmatrix}.
\]
This faithful operator is unit triangular, has determinant \(1\), and has all eigenvalues \(1\), but its displacement from the identity has generic rank \(2\), not \(1\).

### \(3\times3\)

Write
\[
D'=
\begin{pmatrix}
1&x_2&x_3\\
y_2&a_{22}&a_{23}\\
y_3&a_{32}&a_{33}
\end{pmatrix},
\qquad
\rho_i=\frac{b_i}{b_1}.
\]

**COMPUTE.**
\[
Q=
\begin{pmatrix}
1&-x_2&-x_3\\
0&1&0\\
0&0&1
\end{pmatrix},
\qquad
P=
\begin{pmatrix}
1&0&0\\
-\rho_2y_2&1&0\\
-\rho_3y_3&0&1
\end{pmatrix}.
\]
Since \(Qe_1=e_1\), the entries used by \(P\) remain \(d''_{i1}=y_i\). We obtain
\[
D'Q=
\begin{pmatrix}
1&0&0\\
y_2&s_{22}&s_{23}\\
y_3&s_{32}&s_{33}
\end{pmatrix},
\qquad
s_{ij}=a_{ij}-y_i x_j.
\]
Consequently
\[
PB(D'Q)
=
B
\begin{pmatrix}
1&0&0\\
0&s_{22}&s_{23}\\
0&s_{32}&s_{33}
\end{pmatrix}.
\]

For next-layer rows \(c_1,c_2,c_3\),
\[
\widetilde c_1=c_1+x_2c_2+x_3c_3,\qquad
\widetilde c_2=c_2,\qquad
\widetilde c_3=c_3.
\]

Thus the coordinate substitution is
\[
a_{ij}\longmapsto s_{ij}=a_{ij}-y_i x_j,
\qquad
c_1\longmapsto c_1+x_2c_2+x_3c_3,
\]
with \(x_i,y_i,c_2,c_3\) fixed. In that ordering it is unit triangular, hence
\[
\det J_\Psi=1.
\]

The nonfaithful same-side product is
\[
PQ=
\begin{pmatrix}
1&-x_2&-x_3\\
-\alpha_2&1+\alpha_2x_2&\alpha_2x_3\\
-\alpha_3&\alpha_3x_2&1+\alpha_3x_3
\end{pmatrix},
\qquad
\alpha_i=\rho_i y_i.
\]
It has determinant \(1\), while, with
\[
\sigma=\alpha_2x_2+\alpha_3x_3,
\]
\[
\chi_{PQ}(\lambda)
=(\lambda-1)\bigl(\lambda^2-(2+\sigma)\lambda+1\bigr).
\]
It is therefore generically non-unipotent, and \(PQ-I\) has generic rank \(2\).

By contrast, the faithful two-sided operator is \(Q^{\mathsf T}\otimes P\); its determinant is
\[
\det(Q^{\mathsf T}\otimes P)
=\det(Q)^3\det(P)^3=1,
\]
and all its eigenvalues are \(1\).

## Q2. Sharp classification

**COMPUTE:** The faithful coordinate map has determinant \(1\) and is unit triangular after ordering the parameter variables before the updated residual and \(c_1\) coordinates. Thus it has all Jacobian eigenvalues \(1\).

**INFER:** The sharp classification is **(b), a single unipotent map**, but not **(a), a single elementary shear**. If the representation language permits only elementary shears, then **(d)** applies at that factorization level: the generic minimum is at least the ordered \(Q\)-then-\(P\) composition.

Option **(c)** describes the artificial same-side product \(PQ\), not the faithfully transcribed two-sided gauge. The reminder about upper-times-lower products is correct but does not justify replacing \(A\mapsto PAQ\) by \(A\mapsto(PQ)A\).

Also, “unit triangular” is not equivalent to “one elementary transvection”: the displayed Jacobian is unit triangular but \(J_\Psi-I\) has generic rank at least \(2\).

## Q3. Chart-slot verdict

**INFER:** If a chart slot stores one arbitrary coordinate map, it may store
\[
\Psi=\Psi_P\circ\Psi_Q
\]
as one function. If the slot promises one elementary shear, that is not faithful: it must store an ordered pair/composite object. Degenerate loci where \(x=0\) or the relevant \(y_i=0\) may collapse, but the symbolic per-node gauge does not.

VERDICT: **Single general unimodular map suffices (indeed it is coordinate-unipotent), but not a single elementary shear; an elementary-shear slot requires the ordered column-then-row composition.**

MOST LIKELY WRONG: “The gauge is one elementary rank-one shear because its Jacobian is triangular.”  
MOST LIKELY WRONG: “The gauge is non-unipotent because the artificial product \(PQ\) is non-unipotent.”  
MOST LIKELY WRONG: “One chart slot cannot hold the gauge unless it stores only one elementary shear.”