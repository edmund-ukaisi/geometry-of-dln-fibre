Short version: the right lower-bound condition is not “lci” and not a condition on the set \(V\) alone. It is the valuation inequality
\[
A_X(E)=h_E+1 \;\ge\; c\,\operatorname{ord}_E(I)
\]
for every relevant divisor \(E\) over \(X\), where \(I=(f_i)\) and \(c=\operatorname{codim} V\). For \(F=\sum_i f_i^2\), \(\operatorname{ord}_E(F)=2\operatorname{ord}_E(I)\), so this is exactly
\[
\frac{h_E+1}{2k_E}\ge \frac c2.
\]

**1. Resolution Criterion**

Let \(\pi:Y\to X\) be a real analytic log-principalization of \(I=(f_i)\):
\[
I\mathcal O_Y=\mathcal O_Y\!\left(-\sum_j k_jE_j\right),\qquad
\operatorname{Jac}_\pi \sim \prod_j y_j^{h_j}.
\]
Because \(F=\sum f_i^2\), after principalization
\[
F\circ\pi=u\prod_j y_j^{2k_j}
\]
with \(u>0\) analytic unit. Hence
\[
\operatorname{rlct}_x(F)=
\min_{\pi(E_j)\ni x,\ k_j>0}\frac{h_j+1}{2k_j}.
\]
This is the real analogue of the standard log-resolution formula for lct’s of ideals. ([arxiv.org](https://arxiv.org/abs/1107.2676))

Thus a clean lower-bound lemma is:

If \(V\) has pure codimension \(c\), and on one log-principalization every divisor \(E_j\) with \(k_j>0\) and center over the region considered satisfies
\[
h_j+1\ge c k_j,
\]
then \(\operatorname{rlct}(F)\ge c/2\).

The divisor over the smooth generic stratum is only the source of the upper bound. Blowing up a smooth codimension-\(c\) center gives \(k=1\), \(h=c-1\), hence ratio \(c/2\). But divisors over deeper singular strata must also satisfy \(h+1\ge ck\). They are exactly where the lower bound can fail.

For a strict transform divisor: if \(c=1\), then \(h=0\), so the condition says \(1\ge k\), hence \(k=1\). This is reducedness along the divisor. If \(c>1\) and \(V\) is pure codimension \(c\), there should be no non-exceptional divisor in \(F^{-1}(0)\); any such divisor would be a codimension-one component of \(V\).

**2. Geometric Hypothesis**

The sharp geometric condition is:

\[
(X,\,c\cdot I_V)\text{ is log canonical}
\]
or, in valuation language,
\[
A_X(E)\ge c\,\operatorname{ord}_E(I_V)
\quad\text{for all divisorial valuations }E.
\]

For \(F=\sum f_i^2\), this gives \(\operatorname{rlct}(F)\ge c/2\). If there is also a smooth reduced real point of \(V\) of codimension \(c\), then the universal upper bound gives equality.

For reduced lci schemes over \(\mathbb C\), inversion of adjunction is the standard structural theorem translating this ambient pair condition into log-canonical singularities of \(V\) itself; in reducible or non-normal settings one should think “semi-log-canonical” rather than normal log-canonical. ([arxiv.org](https://arxiv.org/abs/math/0209392))

Weighing your candidates:

- **Normal crossings:** sufficient, far from necessary. It gives the divisor inequality directly.
- **lci plus smooth singular strata:** not sufficient. Smoothness of strata does not control infinitely near divisors.
- **Newton nondegeneracy:** good computational sufficient condition, coordinate-dependent, not necessary. For nondegenerate mappings, Newton data can give candidate poles/lct data via log-principalization. ([arxiv.org](https://arxiv.org/abs/math/0601336))
- **Equimultiple/quadratic along strata:** neither sufficient nor necessary. It checks only first-order multiplicity along chosen strata, not all divisorial valuations.

Also, a condition on the set \(V\) alone cannot suffice unless you control the ideal. Same zero set, different powers, different RLCT.

**3. Complete Intersections Do Not Suffice**

False: a real analytic complete intersection need not have \(\operatorname{rlct}=c/2\).

Simplest nonreduced example:
\[
f=x^m,\qquad F=x^{2m},\qquad V=\{0\}\subset\mathbb R.
\]
Then \(c=1\), but
\[
\operatorname{rlct}_0(F)=\frac1{2m}<\frac12.
\]
Here \(f\) is a regular sequence of length \(1\), so “regular sequence” alone is much too weak.

Reduced hypersurface example:
\[
f=x^2-y^3,\qquad F=f^2.
\]
The cusp is reduced lci of codimension \(1\). The weighted valuation with weights \(w(x)=3,w(y)=2\) has
\[
\operatorname{ord}_E(f)=6,\qquad A(E)=3+2=5,
\]
so
\[
\operatorname{rlct}_0(F)=\frac{5}{12}<\frac12.
\]

Even “quadratic leading term for \(F\)” is not enough:
\[
I=(x,\ y^2-z^3)\subset\mathbb R\{x,y,z\},\qquad
F=x^2+(y^2-z^3)^2.
\]
This is a reduced lci of codimension \(2\), and \(F\) has multiplicity \(2\) at the origin. But integrating first in \(x\) reduces the threshold to
\[
\frac12+\operatorname{rlct}\bigl((y^2-z^3)^2\bigr)
=\frac12+\frac{5}{12}
=\frac{11}{12}<1=\frac c2.
\]
So higher singularities genuinely matter.

**4. Citation Practice**

For a specific variety, the cleanest citable route is usually one of these:

1. Exhibit a log-principalization and give a divisor table with \(k_j,h_j\), checking \(h_j+1\ge ck_j\) for every divisor.
2. If equations are Newton-nondegenerate, cite the Newton-polyhedron theorem and show the Newton inequalities.
3. If \(V\) is known structurally to be reduced lci with lc/slc singularities, cite inversion of adjunction and conclude \( \operatorname{lct}(I_V)=c\), hence \(\operatorname{rlct}(\sum f_i^2)=c/2\).

For Lean, I would expose the resolution-ratio lemma as the thin interface. Treat “normal crossing”, “Newton nondegenerate”, and “lc/slc lci” as separate ways of producing the required inequality, not as interchangeable definitions of the mild case.