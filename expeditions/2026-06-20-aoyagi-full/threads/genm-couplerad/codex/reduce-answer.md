1. R1: algebraically correct, with a domain caveat

Let \(S=Q_bQ_b^{T}\). Since
\[
I-\Pi=Q_b^{T}S^{-1}Q_b,
\]
we have
\[
Q=Q\Pi+\widetilde A_zQ_b.
\]
Consequently,
\[
PQ+BQ_b=P(Q\Pi)+(B+P\widetilde A_z)Q_b
       =PY+\widetilde BQ_b .
\]
The cross term vanishes:
\[
\langle PY,\widetilde BQ_b\rangle_F
 =\operatorname{tr}\!\left(PQ\Pi Q_b^T\widetilde B^T\right)=0,
\]
because \(\Pi Q_b^T=0\). Thus
\[
f=\|PY\|_F^2+\|CY\|_F^2+\|\widetilde BQ_b\|_F^2
 =\|EY\|_F^2+\|\widetilde BQ_b\|_F^2.
\]

The change \(B\mapsto\widetilde B=B+P\widetilde A_z\) has unit Jacobian for fixed \((z_0,P)\).

There is, however, a literal domain caveat:
\[
\widetilde B\in[-1,1]^{u\times b}+P\widetilde A_z.
\]
This transformed domain depends on \(z_0\), possibly through kernel directions not determined by \(Y\). Hence the integrand, but not the transformed integration domain, factors exactly through \(Y\).

2. R2: surjectivity is correct; exact product-box factorization is not

For each row,
\[
v\longmapsto v(Z\Pi)
\]
has image \(\operatorname{row}(Z\Pi)\), of dimension \(d\), and kernel dimension \(M_2-d\). Taking \(u\) rows gives a surjection
\[
\mathbb R^{u\times M_2}\twoheadrightarrow
\bigl(\operatorname{row}(Z\Pi)\bigr)^u\simeq\mathbb R^{u\times d}
\]
with kernel dimension \(u(M_2-d)\).

The image of the \(z_0\)-box is generally a zonotope, not a Cartesian product of a fixed \(Y\)-box and a fixed kernel box. Thus the displayed equality with a single constant \(C_1\) is not literally valid.

It is valid for integrability purposes. After choosing a linear complement to the kernel, the transformed \(z_0\)-domain:

- is contained in a bounded product box;
- contains a product neighborhood of \((Y,K)=(0,0)\);
- has constant nonzero coordinate Jacobian.

Likewise, near \(z_0=P=0\), the shifted \(\widetilde B\)-domain contains a fixed neighborhood of \(0\), while globally it remains bounded. These inner/outer comparisons prove that the original integral has exactly the same finiteness threshold as the rectangular multiplication-loss integral. The boundary of the \(Y\)-image causes no additional singularity because \(0\) is an interior point.

3. R4: the free block adds \(ub\)

Since \(S=Q_bQ_b^T\) is positive definite,
\[
\|\widetilde BQ_b\|_F^2
=\operatorname{tr}(\widetilde BS\widetilde B^T)
=\|W\|_F^2
\]
after an invertible linear change \(W=\widetilde BS^{1/2}\). Thus \(W\) has \(k=ub\) independent Gaussian coordinates.

The standard suspension rule gives
\[
\operatorname{RLCT}\bigl(\|EY\|^2+\|W\|^2\bigr)
=\operatorname{RLCT}(\|EY\|^2)+\frac{ub}{2}.
\]
Therefore, if \(\Lambda\) denotes twice the RLCT of \(\|EY\|^2\),
\[
I<\infty\quad\Longleftrightarrow\quad 2q<ub+\Lambda.
\]
At equality the integral diverges.

4. Two-layer RLCT and comparison with \(\phi\)

Put
\[
M=u+a,\qquad H=u,\qquad N=d,\qquad m=\min(u,d).
\]
The Aoyagi–Watanabe two-layer formula gives
\[
\boxed{\displaystyle
\Lambda=\min_{0\le r\le m}
\left\{ud+r^2+(a-d)r\right\}.}
\]

Equivalently,
\[
\Lambda=
\begin{cases}
ud, & d\le a,\\[2mm]
ud-\left\lfloor\dfrac{(d-a)^2}{4}\right\rfloor,
   & a<d<a+2u,\\[3mm]
u(u+a), & d\ge a+2u.
\end{cases}
\]

Now
\[
\phi(\ell)-ub=(u+a)m+\ell^2+(d-2u-a)\ell.
\]

If \(d\ge u\), then \(m=u\), and substituting \(r=u-\ell\) gives exactly
\[
\phi(\ell)-ub=ud+r^2+(a-d)r.
\]
Hence
\[
\min_\ell\phi(\ell)=ub+\Lambda
\qquad(d\ge u).
\]

If \(0<d<u\), the formula does not agree. The correct reparametrization \(r=d-\ell\) yields
\[
\Lambda
=\min_{0\le\ell\le d}
\left\{(u+a)d+\ell^2-(d+a)\ell\right\}.
\]
The supplied expression instead has coefficient \(d-2u-a\), missing
\[
2(u-d)\ell.
\]
For example, \(u=3,a=0,d=1\) gives \(\Lambda=3\), while the supplied minimum is \(-1\).

Conclusion: the finiteness reduction to the arity-3 multiplication loss is valid after replacing the claimed exact product-box equalities by bounded-domain comparisons. It dissolves the stratification. The stated stratified formula agrees only when \(d\ge u\) (and trivially \(d=0\)); for \(0<d<u\), the gap is in \(\phi\), not in the repaired RLCT reduction. No genericity beyond the stated rank and row-space assumptions is needed.