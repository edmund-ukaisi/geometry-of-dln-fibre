## Verdict

**SURVIVES.** At \((4,4,4)\), \(t=(2,0)\), the two radial scales are initially incomparable, but their common corner is blown up. The resulting divisor \(E\) divides every generator. No incomparable \(b_i,b_j\) remain on a terminal chart.

This means “principal” only after pullback to the resolution—not in the original coordinates.

## Exact \((4,4,4)\) calculation

Write

\[
C^1=\begin{pmatrix}A&B\\ C&D\end{pmatrix},\qquad A\in\operatorname{GL}_2.
\]

With

\[
\Delta=D-CA^{-1}B,
\]

invertible block operations give

\[
LC^1R=\operatorname{diag}(I_2,\Delta).
\]

Writing

\[
R^{-1}C^2=\binom{T}{S},
\qquad T,S\in\operatorname{Mat}_{2\times4},
\]

gives the exact ideal identity

\[
\langle C^1C^2\rangle
=
\left\langle
\binom{T}{\Delta S}
\right\rangle .
\]

Thus two pivots are peeled. The structure is precisely:

- two bare pivot rows \(T\), a free \(2\times4\) block;
- one coupled \((2,2,4)\)-heart \(\Delta S\).

They use disjoint coordinates, but they are not two independent singular matrix hearts.

Radialize

\[
T=q\bar T,\qquad \bar t_{11}=1,\qquad J_T=q^7,
\]

and

\[
\Delta=a
\begin{pmatrix}1&u\\v&w\end{pmatrix},
\qquad J_\Delta=a^3.
\]

Setting

\[
\sigma_j=s_{1j}+us_{2j},\qquad e=w-vu,
\]

invertible row operations give

\[
\langle \Delta S\rangle
=
\langle a\sigma_j,\;ae\,s_{2j}:1\le j\le4\rangle .
\]

Hence, before joining,

\[
I=(q,\;a\sigma_j,\;ae\,s_{2j}),
\]

which is genuinely non-principal.

Blow up \(\{q=a=0\}\). In the \(q\)-chart,

\[
q=E,\qquad a=E\alpha.
\]

Therefore

\[
I=(E,\;E\alpha\sigma_j,\;E\alpha e\,s_{2j})=(E).
\]

The Jacobian is

\[
q^7a^3E=E^{11}\alpha^3,
\]

so the \(E\)-divisor gives

\[
\frac{11+1}{2}=6.
\]

This equals \(\minAdm/2=12/2=6\).

## Exact terminal \(b\)-vector

Continuing the same chart to a full diagonal form gives, up to analytic units and permutations,

\[
\boxed{
(b_1,b_2,b_3,b_4)
=
(E,\;E\rho,\;E\rho\beta\nu,\;E\rho\beta\nu\delta\omega)
}.
\]

Here:

- after the first pivot, the remaining bare row is radialized by \(\rho\), with \(\alpha=\rho\beta\);
- \(\bar\Delta\) is reduced to \(\operatorname{diag}(1,e)\);
- a first row \((x,y)=s(1,\xi)\) is radialized and joined with \(e\) by \(s=\nu,\ e=\nu\delta\);
- \(\omega=\tau-z\xi\) is the final scalar Schur complement.

Thus

\[
\frac{b_2}{b_1}=\rho,\qquad
\frac{b_3}{b_2}=\beta\nu,\qquad
\frac{b_4}{b_3}=\delta\omega,
\]

all polynomial monomials. Consequently,

\[
\langle\operatorname{diag}(b)\rangle=(E)
\]

and

\[
\sum_i b_i^2
=
E^2\left(1+\rho^2+\rho^2\beta^2\nu^2+
\rho^2\beta^2\nu^2\delta^2\omega^2\right),
\]

whose parenthesized factor is a unit.

Strictly, the original Frobenius norm need not equal this displayed sum after non-orthogonal block operations; the two sums of squares are analytically comparable and have the same RLCT.

## Newton-polyhedron cross-check

For the intermediate non-principal ideal, normalize a monomial valuation by

\[
x\ge1,\qquad y+s_j\ge1,\qquad y+r+z_j\ge1,
\]

where \(x=w_q,\ y=w_a,\ r=w_e\). Its exact objective is

\[
\frac12\left(8x+4y+\sum_js_j+r+\sum_jz_j\right).
\]

The minimum is attained at

\[
x=y=1,\qquad s_j=r=z_j=0,
\]

and equals

\[
\frac{8+4}{2}=6.
\]

This minimizing ray is exactly the joined divisor \(E\). Thus the Newton polyhedron is needed before the corner blow-up, but not after terminal principalization.

## Why no width vector breaks the chain

Let

\[
U_k=\prod_{\widetilde t(u)=k}u.
\]

Every terminal Aoyagi chart has

\[
b_i=\prod_{k=0}^{i-1}U_k.
\]

A newly introduced exceptional coordinate with threshold \(k\) multiplies the suffix

\[
b_{k+1},b_{k+2},\ldots
\]

and no earlier entry. Therefore

\[
b'_i=
\begin{cases}
b_i,&i\le k,\\
u\,b_i,&i>k,
\end{cases}
\]

which preserves divisibility at every step. Independent radial scales may appear temporarily, but their common-zero corner is subsequently blown up; that creates a shared prefix rather than incomparable terminal factors.

Hence there is **no minimal breaking width vector** within Aoyagi’s completed resolution. Locally the RLCT is read from \(b_1^2\); globally one minimizes the corresponding single-monomial divisor ratios over terminal charts:

\[
\operatorname{rlct}
=
\frac12\min_t Mval(M,t).
\]

The \((4,4,4)\) result above is exact symbolic algebra. The all-width conclusion is the inductive suffix-update argument, not an exhaustive computational search.