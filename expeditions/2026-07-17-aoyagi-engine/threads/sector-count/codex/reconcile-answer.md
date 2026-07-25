Let
\[
\beta_{S,p}(z)_p=z_p,\qquad
\beta_{S,p}(z)_j=z_pz_j\quad(j\in S\setminus\{p\}),
\]
with spectators fixed. Then
\[
\det D\beta_{S,p}(z)=\pm z_p^{|S|-1}.
\]

## Q1 — Why the four charts fail

**Verdict: FACT — yes for this composite, with one qualification to the proposed general principle.**

Write
\[
F=\mathrm{shearH}\circ\mathrm{permP}\circ\mathrm{bbA0}\circ\mathrm{bbA1}.
\]
Since \(g_p=\beta_{S,p}\circ F\),
\[
\det Dg_p(u)=\pm F_p(u)^{|S|-1}\det DF(u).
\]
Here \(|S|=9\) and \(\det DF=-u_0^7u_1^3\). Thus, for \(p=4\),
\[
\det Dg_4
=\pm u_0^7u_1^3\bigl(u_0u_1+u_8u_{10}\bigr)^8.
\]
The second factor is not a coordinate monomial. For example, at
\[
u_0=u_1=u_8=\varepsilon,\qquad u_{10}=-\varepsilon,
\]
with every other coordinate nonzero, it vanishes although no coordinate vanishes. A coordinate monomial cannot do that. The same argument applies to \(p=5,6,7\).

Order matters: this formula is for \(\beta\circ\phi\). If the order were \(\phi\circ\beta\), then \(\det D\phi=1\) would leave the blow-up monomial unchanged.

**FACT — exact general criterion.** On an already constructed chart \(K\), pivot \(p\) is valid precisely when
\[
(\phi_p\circ K)
\]
is a coordinate monomial, or conventionally a coordinate monomial times a nowhere-zero analytic unit, compatible with the existing exceptional divisors. “\(\phi\) fixes \(p\)” is a sufficient way to ensure this, and for an elementary additive shear acting directly on \(p\) it is necessary for a literal pure monomial. It is not the invariant general criterion: what matters is the pulled-back pivot coordinate.

Thus the faithful construction must fan the pair
\[
(\text{pivot }p,\ \text{normalization fixing }p),
\]
not change the pivot while reusing one fixed shear.

## Q2 — Coverage after deleting the four pivots

**Verdict: FACT — no. The remaining 160 charts do not cover any ambient neighbourhood of the origin, even up to measure zero.**

Set
\[
V=\{0,1,2,3,20\},\qquad W=\{4,5,6,7\}.
\]
On any compact source box for a valid outer chart with pivot \(p\in V\), polynomial boundedness gives some \(C_p<\infty\) such that
\[
|x_w|\le C_p|x_p|\le C_p\max_{v\in V}|x_v|,
\qquad w\in W.
\]
For the finite surviving family, take \(C=\max C_p\). Its union is contained in
\[
\max_{w\in W}|x_w|\le C\max_{v\in V}|x_v|.
\]
Consequently the open cone
\[
\max_{w\in W}|x_w|>C\max_{v\in V}|x_v|
\]
escapes every surviving chart. It has positive measure in every ball.

A concrete witness is \(x=t e_4\), \(t\ne0\). It is reached by the outer \(p=4\) chart from incoming point \(t e_4\). But in every \(p\in V\) chart, \(x_p=0\) forces every coordinate in the outer center to be zero, contradicting \(x_4=t\).

The proposed bound
\[
|x_j|\le M|x_{20}|
\]
is a necessary property of points already known to lie in the pivot-20 chart. It cannot establish membership in that chart. For a point coming from the pivot-4 chart,
\[
\frac{x_4}{x_{20}}=\frac1{y_{20}},
\]
which is unbounded as \(y_{20}\to0\), and at \(y_{20}=0\) pivot-20 representation is impossible.

Scaling does not help: these cones are scale-invariant and meet every ball. Thus homogeneity localises the obstruction to the origin rather than removing it.

Whether the specific ray \(t e_4\) lies in the zero fibre requires the explicit coordinate formula for the loss. The ambient-neighbourhood and positive-measure coverage failures do not require that datum.

## Q3 — Repeated pivots

**Verdict: INFERENCE — among the two proposed readings, (i) is the default for a genuine branch; (ii) is not generally true. A third possibility is especially plausible here: the Cartesian repeated-pivot branch is not an affine chart of the genuine transformed-center blow-up.**

For \(S_1\subset S_0\) and a repeated pivot \(q\in S_1\),
\[
\beta_{S_0,q}\circ\beta_{S_1,q}
\]
has
\[
x_q=u_q,\qquad
x_j=u_q^2u_j\ (j\in S_1\setminus\{q\}),\qquad
x_k=u_qu_k\ (k\in S_0\setminus S_1),
\]
so the Jacobian powers add:
\[
(|S_0|-1)+(|S_1|-1)=7+3=10.
\]

But \(10+1=11\) is only a discrepancy numerator, not automatically a binding exponent. If the pulled-back ideal has order \(N_q\) along \(u_q=0\), the candidate for a squared loss is
\[
\frac{10+1}{2N_q}.
\]
The divisor might instead be absent from the dominant ideal monomial, or another axis might bind. Therefore the set \(\{8,9,12\}\) cannot decide this without the explicit pulled-back ideal.

**FACT — repeated-pivot images are not generally redundant.** The point \(t e_q\) lies in the repeated-pivot chart. It lies in no naïve distinct-pivot two-level chart:

- If the outer pivot \(p_0\ne q\), then \(x_{p_0}=0\) forces \(x_q=0\).
- If \(p_0=q\) and the inner pivot \(p_1\ne q\), then \(x_{p_1}=x_q u_{p_1}=0\) forces \(u_{p_1}=0\), hence \(x_q=0\).

So image containment cannot be assumed.

There is also a transformed-center issue. If the second center is the strict transform of \(Z(S_1)\) after blowing up \(Z(S_0)\), then in an outer \(q\)-chart with \(q\in S_1\), that strict transform is empty: the equation \(x_q=0\) pulls back to the exceptional coordinate itself, and saturation gives the unit ideal. In that situation no second pivot \(q\)—indeed no second blow-up there—exists. The first-level \(q\)-chart already covers that region.

To decide exactly, one needs:

1. the center ideal on every preceding chart and whether strict, weak, or total transforms are used;
2. the admissible pivot set after that transform;
3. the full pullback of the loss ideal and its divisibility-minimal monomial;
4. the actual compact chart domains for any claimed image containment.

## Q4 — \(\theta\) and atlas size

**Verdict: FACT — \(\theta=1\) gives no atlas-size prediction.**

\(\theta\) counts top-dimensional irreducible components of the fibre. Chart count depends on the blow-up centers, their affine covers, branch-dependent transforms, and optional refinements. It is not a birational invariant and can be increased by duplicating or subdividing charts.

The paper-faithfulness test is:

- every chart is an actual affine chart of the stated blow-up sequence;
- its normalization is adapted to its pivot;
- both the pulled-back ideal and Jacobian have the required normal-crossings form;
- the chart family covers the required neighbourhood or exceptional preimage.

**FACT:** \(160=4\cdot8\cdot5\) is ruled out by Q2.

**INFERENCE:** If the three pivot choices truly are independent affine-chart choices, the most natural repair retains 288 chart slots and replaces the 128 bad maps by pivot-adapted normalizations. Their directions are needed; their present shears are wrong.

If transformed centers or case-dependent admissibility restrict the Cartesian product, the genuine number may be smaller, but it cannot be calculated from the supplied data. The explicit branch tree and transformed center ideals are the missing datum. Thus the 128 failures show drift in the fixed-shear fan construction, not by themselves overproduction in chart count.