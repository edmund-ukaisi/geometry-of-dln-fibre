## Verdict

| Step | Role in \((3,3,4)\) | Source-map determinant |
|---|---|---:|
| \(Q_1\) acting literally on \(C_1\) | Non-invertible; in the product it is an ideal-generator/output-row cofactor | Literal map: \(0\). No contribution to \(Dg\) |
| \(Q_2\) acting literally on \(C_1\) | Non-invertible | \(0\) |
| Absorbing \(Q_2^{-1}\) into \(C_2\) | Genuine invertible source-coordinate shear | \(1\) |
| \(C_{22}\mapsto\Delta=C_{22}-C_{21}C_{12}\) | Genuine invertible source-coordinate shear | \(1\) |

Thus the all-the-way chart map to the original weights is not purely monomial: it contains polynomial shears. Nevertheless, its absolute Jacobian is a pure exceptional monomial with coefficient/unit exactly \(1\).

## Direct algebra

Write

\[
C_1=
\begin{pmatrix}
1&A\\ B&M
\end{pmatrix},\qquad
A=(a_1,a_2),\quad B=(b_1,b_2)^T .
\]

Then

\[
Q_1=\begin{pmatrix}1&0\\-B&I_2\end{pmatrix},
\qquad
Q_2=\begin{pmatrix}1&-A\\0&I_2\end{pmatrix},
\]

and direct multiplication gives

\[
Q_1C_1Q_2=
\begin{pmatrix}
1&0\\0&M-BA
\end{pmatrix}
=\operatorname{diag}(1,\Delta).
\]

Both \(Q_i\) are unipotent, but that alone says nothing about the Jacobian of the coordinate-dependent nonlinear operation.

### \(Q_1\)

Directly,

\[
Q_1C_1=
\begin{pmatrix}
1&A\\0&\Delta
\end{pmatrix}.
\]

As a map on the eight nonpivot entries,

\[
(A,B,M)\longmapsto(A,0,\Delta).
\]

Its Jacobian has rank \(6\) and determinant \(0\): it clears \(B\). Thus \(C_1\mapsto Q_1C_1\) is not a coordinate change.

For the product,

\[
C_1C_2
=Q_1^{-1}\operatorname{diag}(1,\Delta)Q_2^{-1}C_2 .
\]

Since \(Q_1^{-1}\) is invertible over the local analytic ring,

\[
\langle (C_1C_2)_{ij}\rangle
=
\left\langle
\left(\operatorname{diag}(1,\Delta)Q_2^{-1}C_2\right)_{ij}
\right\rangle .
\]

So in this boundary position \(Q_1^{-1}\) is an output-row/generator cofactor, not part of \(g\), and contributes no source Jacobian.

### \(Q_2\)

Literal multiplication gives

\[
C_1Q_2=
\begin{pmatrix}
1&0\\B&\Delta
\end{pmatrix}.
\]

Thus

\[
(A,B,M)\longmapsto(0,B,\Delta)
\]

also has rank \(6\) and determinant \(0\): it clears \(A\).

But this is not how \(Q_2\) is used in the product. Write

\[
C_2=\begin{pmatrix}X\\S\end{pmatrix},
\qquad X\in\mathbb R^{1\times4},\quad S\in\mathbb R^{2\times4}.
\]

Then

\[
Q_2^{-1}C_2
=
\begin{pmatrix}X+AS\\S\end{pmatrix}
=
\begin{pmatrix}T\\S\end{pmatrix}.
\]

The source-coordinate map

\[
(A,X,S)\longmapsto(A,T=X+AS,S)
\]

is triangular, with inverse \(X=T-AS\), and

\[
\det\frac{\partial(A,T,S)}{\partial(A,X,S)}=1.
\]

Hence the absorbed \(Q_2^{-1}\) is a genuine source-coordinate shear with Jacobian exactly \(1\).

### Schur complement

Retaining \(A,B\), define

\[
(A,B,M)\longmapsto(A,B,\Delta=M-BA).
\]

Its Jacobian has block form

\[
\begin{pmatrix}
I_4&0\\ *&I_4
\end{pmatrix},
\]

so its determinant is exactly \(1\). Its inverse is

\[
M=\Delta+BA.
\]

This is the honest coordinate change that preserves the variables cleared by the formal row/column operations.

Combined,

\[
(A,B,M,X,S)\longleftrightarrow(A,B,\Delta,T,S)
\]

has determinant \(1\) in both directions.

## Full \((3,3,4)\) Jacobian

Choose radial charts

\[
T=q\,\tau,\qquad \tau=(1,r_2,r_3,r_4),
\]

and

\[
\Delta=u\,\widehat D,\qquad
\widehat D=
\begin{pmatrix}1&d_{12}\\d_{21}&d_{22}\end{pmatrix}.
\]

Their determinants are

\[
|\det D(T\text{-radial})|=|q|^3,\qquad
|\det D(\Delta\text{-radial})|=|u|^3.
\]

In the \(q\)-leading join chart,

\[
q=E,\qquad u=E\alpha,
\]

whose two-dimensional Jacobian is \(|E|\). Therefore

\[
|\det Dg_{\mathrm{normalized}}|
=
|q|^3|u|^3|E|
=
|E|^7|\alpha|^3.
\]

The complete inverse chart is explicitly

\[
C_1=
\begin{pmatrix}
1&A\\
B&E\alpha\widehat D+BA
\end{pmatrix},
\qquad
C_2=
\begin{pmatrix}
E\tau-AS\\S
\end{pmatrix}.
\]

A direct \(20\times20\) symbolic determinant gives

\[
\det Dg_{\mathrm{normalized}}=-E^7\alpha^3,
\]

the sign being only coordinate orientation. Thus the absolute Jacobian is a pure monomial with unit identically \(1\), despite \(g\) itself containing the nonmonomial terms \(BA\) and \(AS\).

In the other join chart \(q=E\beta,\ u=E\),

\[
|\det Dg_{\mathrm{normalized}}|=|E|^7|\beta|^3.
\]

There is one scope correction: \(c_{11}=1\) is a normalized blow-up coordinate, not an original weight value near the deepest point. If the preceding blow-up of all nine \(C_1\) entries is included,

\[
C_1^{\mathrm{original}}=\rho\,C_1^{\mathrm{normalized}},
\]

and it contributes \(|\rho|^8\). Hence the actual map to the original weights has

\[
\boxed{|\det Dg|=|\rho|^8|E|^7|\alpha|^3}
\]

in the first join chart. The often-quoted \(|E|^7|\alpha|^3\) is relative to the already normalized \(c_{11}=1\) chart.

The loss unit is generally nontrivial:

\[
F\circ g=\rho^2E^2\,
\left\|Q_1^{-1}
\begin{pmatrix}\tau\\ \alpha\widehat D S\end{pmatrix}
\right\|_F^2.
\]

That analytic factor is not identically \(1\); this does not contradict the Jacobian unit being exactly \(1\).

## Corank comparison

There is no qualitative change at corank \(2\). For the clean \(2\times2\) step,

\[
D=\begin{pmatrix}1&a\\b&c\end{pmatrix},
\qquad w=c-ba,
\]

the retained-coordinate map

\[
(a,b,c)\mapsto(a,b,w)
\]

has determinant \(1\), whereas the literal maps \(D\mapsto Q_1D\) and \(D\mapsto DQ_2\) each have determinant \(0\).

The same block-triangular calculation holds for arbitrary residual size:

\[
D=\begin{pmatrix}1&A\\B&M\end{pmatrix},
\qquad M\mapsto M-BA.
\]

Higher corank changes the number of subsequent blocks, exceptional variables, and monomial exponents—not whether the shears are coordinate changes or whether they introduce Jacobian units.

Computed facts above include all displayed matrix identities, ranks, and the direct \(20\times20\) and \(21\times21\) determinants. The extension to every Aoyagi chart is conditional only on the stated recursion using normalized unipotent elimination and monomial blow-ups; I did not independently verify from the primary text that no additional non-unipotent rescaling is inserted elsewhere.