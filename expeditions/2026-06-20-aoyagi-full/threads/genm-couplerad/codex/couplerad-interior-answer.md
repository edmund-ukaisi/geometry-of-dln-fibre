Assume the box is \([-1,1]\) in every free coordinate, hence contains the origin.

## Q1

Let \(z=(\operatorname{vec}X,\operatorname{vec}Y)\).

### (a) Rank

Using column-wise vectorization,
\[
\operatorname{vec}(XS)=(S^\top\!\otimes I_u)\operatorname{vec}X,
\qquad
\operatorname{vec}(YK)=(K^\top\!\otimes I_a)\operatorname{vec}Y.
\]
Hence
\[
f(z)=z^\top
\begin{pmatrix}
(S^\top\!\otimes I_u)^\top(S^\top\!\otimes I_u)&0\\
0&(K^\top\!\otimes I_a)^\top(K^\top\!\otimes I_a)
\end{pmatrix}z,
\]
so \(f\) is PSD. Since \(\operatorname{rank}(A^\top A)=\operatorname{rank}(A)\),
\[
\boxed{\rho=u\,r_S+a\,r_K}.
\]

### (b) Exact threshold

After orthogonal diagonalization, \(f\) is comparable to
\[
t_1^2+\cdots+t_\rho^2
\]
in its \(\rho\) active directions. Radial integration there gives
\[
\int_0^\varepsilon r^{\rho-1-2q}\,dr<\infty
\quad\Longleftrightarrow\quad
2q<\rho.
\]
Therefore
\[
\boxed{\int_B f^{-q}<\infty
\iff q<\frac{u r_S+a r_K}{2}.}
\]
If \(\rho=0\), \(f\equiv0\), so no \(q>0\) is admissible.

### (c) Load-bearing gap

The \(Y\)-only form has rank \(a r_K\), so
\[
\int \|YK\|_F^{-2q}\,dY<\infty
\iff q<\frac{a r_K}{2}.
\]
Consequently, the \(Y\)-only integral diverges while the sum remains finite exactly when
\[
\boxed{\frac{a r_K}{2}\le q<
\frac{a r_K+u r_S}{2},\qquad q>0.}
\]
This interval is nonempty exactly when \(r_S>0\) (assuming \(u>0\)). If \(r_K=0\), it becomes
\[
0<q<\frac{u r_S}{2}.
\]

### (d) Excluding singular \(X\)

No. Removing the determinant-zero locus removes only a Lebesgue-null set, so the integral of the nonnegative measurable integrand—and therefore its threshold—is unchanged.

---

## Q2

Put
\[
p=b-1,\qquad d=ap,\qquad
\kappa=W+\|R\Pi\|_F^2.
\]

### (a) Orthogonal decomposition and Jacobian

Since \(\Pi\) projects onto \(\operatorname{row}(B)^\perp\),
\[
R+\Gamma B
=R\Pi+\bigl(R(I-\Pi)+\Gamma B\bigr).
\]
Every row of \(R\Pi\) lies in \(\operatorname{row}(B)^\perp\), while every row of the parenthesized term lies in \(\operatorname{row}(B)\). Thus the two matrices are Frobenius-orthogonal, giving
\[
\boxed{\|R+\Gamma B\|_F^2
=\|R\Pi\|_F^2+
\|R(I-\Pi)+\Gamma B\|_F^2.}
\]

For each row, the bijection
\[
\gamma\in\mathbb R^p\longmapsto \gamma B\in\operatorname{row}(B)
\]
has Gram matrix \(BB^\top\), hence Jacobian
\[
\sqrt{\det(BB^\top)}.
\]
For \(a\) independent rows, the Jacobian is
\[
\boxed{\det(BB^\top)^{a/2}}.
\]

### (b) Closed form and convergence

Changing to orthonormal coordinates \(z\in\mathbb R^d\) on the \(a\) copies of \(\operatorname{row}(B)\),
\[
J=\det(BB^\top)^{-a/2}
\int_{\mathbb R^d}(\kappa+\|z\|^2)^{-c'}\,dz.
\]
If \(\kappa>0\), this is finite exactly when \(c'>d/2\), and
\[
\boxed{
J=\det(BB^\top)^{-a/2}
\pi^{d/2}\frac{\Gamma(c'-d/2)}{\Gamma(c')}
\kappa^{-(c'-d/2)}.
}
\]
Thus
\[
\boxed{\operatorname{Cst}(a,b-1,c')
=\pi^{a(b-1)/2}
\frac{\Gamma\!\left(c'-a(b-1)/2\right)}{\Gamma(c')}.}
\]

If \(d>0\) and \(\kappa=0\), \(J=\infty\) for every real \(c'\): convergence near zero requires \(c'<d/2\), while convergence at infinity requires \(c'>d/2\).

### (c) Exponent reduction

Integration over \(\Gamma\) reduces the exponent by half the integrated dimension:
\[
\boxed{c''=c'-\frac{a(b-1)}2.}
\]

For the degenerate case \(d=0\), there is no integration: \(J=\kappa^{-c'}\) whenever that quantity is defined and finite.