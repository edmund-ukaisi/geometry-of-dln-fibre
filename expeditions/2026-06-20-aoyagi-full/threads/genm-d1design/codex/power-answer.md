The requested clean factorization is false. The rank-\(1\) blow-up produces the charge \(2\), but also an unavoidable Gram weight. Plain \(hIH\) cannot absorb it; a further joint source–tail incidence resolution is required.

## (a) Sector/chart — PROVEN

Write
\[
F=
\begin{pmatrix}
x&y_1&y_2\\
ux&uy_1+\delta_1&uy_2+\delta_2
\end{pmatrix},
\]
on a rank-\(1\) pivot chart where \(x=f_{11}\) is bounded away from \(0\). Explicitly,
\[
u=\frac{f_{21}}{f_{11}},\qquad
\delta_1=f_{22}-u f_{12},\qquad
\delta_2=f_{23}-u f_{13}.
\]
Thus
\[
\delta_1=\frac{\det P}{f_{11}},
\]
and \(F\) has limiting rank \(1\) precisely when
\[
\delta_1=\delta_2=0.
\]

If the rows of \(A_1\) are \(a_0,a_1,a_2\in\mathbb R^{1\times3}\), set
\[
B=xa_0+y_1a_1+y_2a_2.
\]
Then
\[
FA_1=
\begin{pmatrix}
B\\
uB+\delta_1a_1+\delta_2a_2
\end{pmatrix}.
\]

On the projective sector \(|\delta_1|\ge|\delta_2|\), use
\[
z=\delta_1,\qquad \eta=\delta_2/\delta_1.
\]
Hence
\[
FA_1=
\begin{pmatrix}
B\\
uB+z(a_1+\eta a_2)
\end{pmatrix}.
\]

The exceptional source normals are therefore
\[
(\delta_1,\delta_2)
=
\left(
f_{22}-\frac{f_{21}}{f_{11}}f_{12},
f_{23}-\frac{f_{21}}{f_{11}}f_{13}
\right).
\]
After blow-up there is one exceptional divisor \(z=0\); \(\eta\) is its projective direction. The variables \(x,y_1,y_2,u,B,a_1,a_2\) are transverse/base variables. Crucially, \((a_1+\eta a_2)Z_{\rm deep}\) is not a unit: its rank-drop requires further incidence charts.

The second projective chart interchanges \(\delta_1,\delta_2\).

## (b) Jacobian — PROVEN

The complete coordinate map uses
\[
a_0=x^{-1}(B-y_1a_1-y_2a_2).
\]
Its Jacobian factors as

\[
\underbrace{|x|}_{F\leftrightarrow(x,y,u,\delta)}
\cdot
\underbrace{|z|}_{(\delta_1,\delta_2)=(z,z\eta)}
\cdot
\underbrace{|x|^{-3}}_{a_0\leftrightarrow B}.
\]

Therefore
\[
\boxed{|\det D\Phi|=|x|^{-2}|z|}.
\]

On a pivot patch \(\kappa\le |x|\le1\), \(u_{\rm Jac}(\xi)=|x|^{-2}\) is bounded above and below. Thus the sole exceptional exponent is
\[
\boxed{\nu_z=2},
\qquad |z|^{\nu_z-1}=|z|.
\]

## (c) Reduction — PROVEN negative result

A bounded row shear removes \(uB\), giving
\[
\|FA_1Z_{\rm deep}\|_F^2
\asymp
X+z^2Y,
\]
where
\[
X=\|BZ_{\rm deep}\|_F^2,\qquad
Y=\|(a_1+\eta a_2)Z_{\rm deep}\|_F^2.
\]

For \(c'>1\),
\[
\begin{aligned}
\int_{-\varepsilon}^{\varepsilon}
 |z|(X+z^2Y)^{-c'}\,dz
&=
\frac{X^{1-c'}-(X+\varepsilon^2Y)^{1-c'}}
     {(c'-1)Y}.
\end{aligned}
\]

Equivalently, the charge-\(2\) radial integral is
\[
\int_{-\infty}^{\infty}|t|(1+t^2)^{-c'}dt
=\frac1{c'-1},
\]
and the scaling gives
\[
X^{-(c'-1)}Y^{-1}.
\]

Thus the shift \(c'\mapsto c'-1\) does appear, but together with
\[
\boxed{Y^{-1}
=\|(a_1+\eta a_2)Z_{\rm deep}\|_F^{-2}}.
\]

Invariantly, with
\[
C=\begin{pmatrix}a_1\\a_2\end{pmatrix},
\qquad Q=CZ_{\rm deep},
\]
normal integration gives
\[
\int_{\mathbb R^2}(X+\|\delta Q\|^2)^{-c'}\,d\delta
=
\frac{\pi}{c'-1}\,
X^{1-c'}\det(QQ^\top)^{-1/2},
\]
when \(Q\) has rank \(2\).

Therefore the stratum does not factor into a convergent radial constant times plain
\[
hIH((1,3,n_{\rm last},\ldots),c'-1).
\]
It leaves the forbidden weight
\[
\det(CZ_{\rm deep}Z_{\rm deep}^{\top}C^\top)^{-1/2}.
\]
Near \(\operatorname{rank}(CZ_{\rm deep})<2\), even this formula degenerates and further joint incidence resolution is necessary.

## (d) General pattern — PROVEN first blow-up; claimed clean reduction REFUTED

Let
\[
m=M_0,\quad n=M_1,\quad p=M_2,\quad
r=m-s,\quad k=n-s,\quad N=rk.
\]
Choose an invertible \(s\times s\) pivot \(X\) and write
\[
F=
\begin{pmatrix}
X&Y\\
UX&UY+\Delta
\end{pmatrix},
\qquad
A_1=\begin{pmatrix}A_0\\C\end{pmatrix},
\qquad
B=XA_0+YC.
\]
Then
\[
FA_1=
\begin{pmatrix}
B\\UB+\Delta C
\end{pmatrix}.
\]

The source CoV has
\[
\left|\det\frac{\partial(F,A_1)}
 {\partial(X,Y,U,\Delta,B,C)}\right|
=
|\det X|^{\,r-p},
\]
a bounded unit on the pivot chart.

Blowing up the \(N=rk\) entries of \(\Delta\) by
\[
\Delta=z\Theta,\qquad \Theta_{i_0j_0}=1,
\]
gives
\[
\boxed{|\det D\Phi|
=u(\xi)|z|^{N-1}},
\qquad
\boxed{\nu_z=N=(M_0-s)(M_1-s)}.
\]

Hence the charge is the codimension of the limiting source-rank locus
\[
\{\operatorname{rank}F\le s\},
\]
not the codimension of \(\{\operatorname{rank}W\le s\}\).

After the row shear,
\[
\|FA_1Z_{\rm deep}\|^2
\asymp
\|BZ_{\rm deep}\|^2+
z^2\|\Theta CZ_{\rm deep}\|^2.
\]
Indeed, if \(Q=CZ_{\rm deep}\) has full row rank,
\[
\int_{\mathbb R^{r\times k}}
(X+\|\Delta Q\|_F^2)^{-c'}d\Delta
=
\pi^{N/2}\frac{\Gamma(c'-N/2)}{\Gamma(c')}
X^{N/2-c'}\det(QQ^\top)^{-r/2}.
\]

So the shift \(c'\mapsto c'-N/2\) always carries a residual Gram divisor. A per-\(s\) determinantal blow-up alone does not reduce to plain \(hIH(\operatorname{redChain}s\,M)\).

Yes, \(M_2=p\) remains in
\[
B\in\mathbb R^{s\times p},
\qquad
\operatorname{redChain}s\,M=(s,p,\ldots).
\]
But the difference from the \(W\)-rank codimension is not literally an “excess codimension” contributed by that reduced layer. It arises because \((F,A_1)\mapsto W\) has singular fibres. Only the recursive threshold arithmetic places the \(M_2\)-dependence in the reduced problem.

## (e) Verdict

**{NEW-BLOWUP} — PROVEN:** the banked fixed-\(F\)+qbox route fails in POWER, while the first rank-\(F\) blow-up still leaves a Gram weight; a genuinely new joint source–tail incidence resolution is required.

Cheapest numerical check: evaluate the full \(15\times15\) Jacobian at \(x=\tfrac12\). It must equal \(4|z|\); changing \(z\) from \(10^{-3}\) to \(10^{-4}\) must change its absolute determinant by exactly a factor \(10\), confirming \(\nu_z=2\).