The honest verdict is mixed: the single seam is benign, and the determinant charge is harmless. The proposed cross-peel additivity is not valid without an injectivity hypothesis; proving that all remaining coupled seams are benign would essentially prove the stated open local conjecture.

## Q1 — [BENIGN]

Put \(q=n-r\) and \(e=d-r\). Define

\[
C(m,q,e):=\min_{0\le s\le \min(m,q)}
\bigl((m-s)(q-s)+se\bigr).
\]

[FACT] On the rank-\(s\) stratum of \(F\),

\[
\dim\{(F,E):FE=0,\ \operatorname{rank}F=s\}
=s(m+q-s)+(q-s)e.
\]

Hence

\[
\operatorname{codim}\{FE=0\}
=\min_s\left[mq+qe-s(m+q-s)-(q-s)e\right]
=C(m,q,e).
\]

[FACT] At the origin,

\[
\boxed{\operatorname{rlct}_0\!\left(\|FE\|_F^2\right)
=\frac{C(m,q,e)}2.}
\]

This follows from the supplied global two-layer DLN theorem: the origin realizes the global RLCT because the multiplication loss and its zero fiber are conic.

More strongly, [FACT] this holds locally at every point of a two-factor zero fiber. If

\[
s=\operatorname{rank}F_0,\qquad
t=\operatorname{rank}E_0,\qquad
u=q-s-t,
\]

then analytic Gaussian elimination around the nonzero pivots gives

\[
\|FE\|^2
\asymp
\|z\|^2+\|F'E'\|^2,
\]

where

\[
\dim z=mt+se-st,\qquad
F'\in\mathbb R^{(m-s)\times u},\quad
E'\in\mathbb R^{u\times(e-t)}.
\]

Thus, using S1, S3, and S4,

\[
\operatorname{rlct}_{(F_0,E_0)}(\|FE\|^2)
=
\frac{mt+se-st+C(m-s,u,e-t)}2.
\]

The numerator is also the local codimension. Therefore a two-layer product never gives a local deficit below codimension/2.

For the complete single-peel model, H is disjoint from \((F,E)\), so S1 and S4 give

\[
\boxed{
\operatorname{rlct}_0\bigl(\|H\|^2+\|FE\|^2\bigr)
=\frac{mr+C(m,q,e)}2.
}
\]

Exact values:

| \((m,q,e)\) | \(C(m,q,e)\) | \(\operatorname{rlct}(\|FE\|^2)\) | Full single-peel RLCT |
|---|---:|---:|---:|
| \((2,1,1)\) | \(1\) | \(1/2\) | \(r+1/2\) |
| \((2,2,2)\) | \(3\) | \(3/2\) | \(r+3/2\) |
| \((3,2,3)\) | \(5\) | \(5/2\) | \(3r/2+5/2\) |
| \((2,3,2)\) | \(4\) | \(2\) | \(r+2\) |

For \(q=1\),

\[
\|FE\|^2=\|F\|^2\|E\|^2,
\]

so S2 directly yields \(\min(m/2,e/2)\). For \(q>1\), S2 does not directly apply because the entries contain sums \(\sum_kF_{ik}E_{kj}\).

## Q2 — [DEPENDS]

[FACT] Shared \(P\) destroys naive S1 additivity. The scalar model already shows it:

\[
K=p^2(h^2+f^2e^2).
\]

By S1, S2, and S4,

\[
\operatorname{rlct}(h^2+f^2e^2)
=\frac12+\min\left(\frac12,\frac12\right)=1,
\]

but then

\[
\operatorname{rlct}(K)=\min\left(\frac12,1\right)=\frac12.
\]

This is not a codimension deficit: \(K^{-1}(0)\) has the component \(\{p=0\}\) of codimension \(1\). It shows that one must minimize over rank paths/components, rather than add every peel contribution.

[FACT] If \(P\in\mathbb R^{a\times m}\), then

\[
\|PX\|\asymp\|X\|
\]

requires \(P\) to have full column rank \(m\), equivalently \(P^TP\succ0\). Full row rank is insufficient when \(a<m\). Because \(H\) is free, restricted injectivity generally cannot replace this condition.

Consequently:

- For \((2,2,2,2)\), a generic square \(2\times2\) head is invertible on the ambient big cell, so S3 reduces the loss to Q1 there.
- For \((2,3,3,3)\), taking the natural left head \(P\in\mathbb R^{2\times3}\), generic full row rank is only rank \(2\); it has a one-dimensional kernel and does not yield S3 comparability.
- A pivot big cell for the peeled last layer imposes no rank condition on the earlier product \(P\).

At the all-zero point, exact answers are nevertheless available. Let \(A\in\mathbb R^{m\times q}\), \(B\in\mathbb R^{q\times d}\), \(C\in\mathbb R^{d\times e}\). The codimension of the rank-\(s\) locus of \(AB\) is

\[
D_s=
\min_{s\le k\le\min(m,q)}
\left((m-k)(q-k)+(k-s)(d-s)\right).
\]

Indeed, rank \(A=k\) costs \((m-k)(q-k)\), and making the effective \(k\times d\) product have rank \(s\) costs \((k-s)(d-s)\). Given rank \(AB=s\), the condition \(ABC=0\) costs \(se\). Therefore

\[
\operatorname{codim}\{ABC=0\}
=\min_s(D_s+se).
\]

This gives:

\[
\begin{array}{c|c|c|c}
\text{widths}&(D_0,D_1,D_2)&\operatorname{codim}\{ABC=0\}
&\operatorname{rlct}_0\\ \hline
(2,2,2,2)&(3,1,0)&\min(3,3,4)=3&3/2\\
(2,3,3,3)&(5,2,0)&\min(5,5,6)=5&5/2
\end{array}
\]

[FACT] The origin values follow from the supplied global theorem plus conicity. Generic points of the minimal components are Morse–Bott and also give \(3/2\) and \(5/2\) by S3–S4.

[INFERENCE] At deeper intersections where \(P\) is noninjective and several rank paths meet, the telescoping-Schur argument alone does not prove equality. Showing that this coupling never lowers the exponent below the correctly minimized local codimension/2 is the open local problem.

## Q3 — [DEPENDS]

[FACT] For genuinely independent quadratic coordinates,

\[
K\asymp\sum_{j=1}^k\sum_{\ell=1}^{e_j}z_{j\ell}^2,
\]

assign block weight \(z_{j\ell}\sim t^{\alpha_j}\). The weighted candidate is

\[
\lambda(\alpha)
=
\frac{\sum_j e_j\alpha_j}{2\min_j\alpha_j}
\ge \frac{\sum_j e_j}{2},
\]

with equality when all \(\alpha_j\) are equal. This is S3–S4, equivalently the Newton-polyhedron calculation.

But [FACT] seam coordinates are not quadratic-nondegenerate at \(F=E=0\). For

\[
K=h^2+f^2e^2,
\]

equal weights give the candidate \(3/2\), while weights

\[
(w_h,w_f,w_e)=(1,\tfrac12,\tfrac12)
\]

give

\[
\frac{1+\frac12+\frac12}
 {2\min(1,\frac12+\frac12)}
=1.
\]

Indeed S1–S2 give the exact RLCT \(1\), equal to codimension/2.

Thus non-comparable sectors can strictly beat comparable scaling, even for a benign DLN seam. They fall below codimension/2 only when genuine higher-order tangency is present; for example \(x^2+y^4\) has weights \((1,\tfrac12)\) and RLCT \(3/4<1\).

## Q4 — [BENIGN]

Let \(G=DD^T\). On the stated compact subchart,

\[
\lambda I\preceq G\preceq\Lambda I.
\]

Therefore

\[
\lambda NN^T
\preceq NGN^T
\preceq\Lambda NN^T.
\]

If \(N\) has \(b\) rows,

\[
\lambda^b\det(NN^T)
\le
\det(NGN^T)
\le
\Lambda^b\det(NN^T).
\]

Consequently,

\[
\Lambda^{-ab/2}\det(NN^T)^{-a/2}
\le
\det(NGN^T)^{-a/2}
\le
\lambda^{-ab/2}\det(NN^T)^{-a/2}.
\]

[FACT] This is a bounded-factor equivalence, so S3 says the charge has exactly the same leading corank exponent. It can fail only when the chart approaches a boundary where the smallest singular value of \(D\) is no longer uniformly positive.

## Q5 — [DEPENDS / OPEN]

[FACT] I cannot construct the requested DLN counterexample. Producing one would disprove the stated local DLN conjecture. Conversely, the inequalities \(a+b\le\rho-1\) and \(1\le j<r\) alone do not imply the injectivity or joint-transversality needed to prove benignity.

[FACT] The cleanest pointwise sufficient condition is

\[
\operatorname{rank}D\mu_x
=
\operatorname{codim}_x\mu^{-1}(0)=C,
\qquad
\mu=(L_{p-1}\cdots L_0).
\]

Then analytic coordinates \(z_1,\dots,z_C\) can be selected from independent components of \(\mu\), and the remaining components lie in the ideal \((z_1,\dots,z_C)\). Hence

\[
\|\mu\|^2\asymp z_1^2+\cdots+z_C^2,
\]

so S3–S4 give

\[
\boxed{\operatorname{rlct}_x=C/2.}
\]

A peelwise sufficient version is: every head coefficient acting on a new transverse block is uniformly injective on the relevant quotient, and the resulting normal blocks are jointly independent. Then the loss is boundedly equivalent to a disjoint sum of squares and S1/S3/S4 apply.

The most likely place for a deficit, if one exists, is a simultaneous intersection of recursive rank strata where the shared head acquires a kernel aligned with both \(H\) and \(FE\), while a spectator \(F\) also loses rank. There the first nonzero normal jet can be a product of several transverse variables, and non-comparable weights become essential. No deficit occurs at a single peel, at generic Morse–Bott points, or from the \(DD^T\) metric factor alone.