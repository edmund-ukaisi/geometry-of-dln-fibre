Your empty hunt certifies only the toroidal divisors of the chosen incidence charts, at generic residue centers. The first genuinely unsearched family is: blow-ups of non-coordinate subvarieties inside their exceptional/zero-weight directions, especially angular incidence or cancellation loci shared by adjacent layers.

## Q1. Which divisors are unreachable?

**Established fact.** A weight vector \(w\) on chart coordinates \(y_i\) reaches precisely valuations that are monomial in those coordinates:

\[
v\!\left(\sum c_m y^m\right)=\min_m \langle w,m\rangle .
\]

This includes every divisor obtained through sequences of toroidal blow-ups—blow-ups of coordinate strata. A second or third toroidal blow-up gives another primitive ray, hence another weight vector already covered by the LP.

It does not include:

- blow-ups of non-coordinate centers;
- valuations made monomial only after introducing a coordinate such as \(h=b g+\delta c\);
- special centers among zero-weight “angular” variables, where coefficient residues satisfy relations;
- residual determinantal centers not converted into coordinate strata by further pivots.

Higher-corank geometry is not intrinsically missed if rank-one Schur pivots are iterated over every residual block. A single peel, however, does not provide that completeness.

**Concrete missed divisor, \((2,2,2,2)\).** In your `h6` chart set

\[
h=1+a_1b_2.
\]

The transformed product contains

\[
\frac{P_{00}}{\alpha_1\alpha_2}=hp+a_1d_2r,\qquad
\frac{P_{01}}{\alpha_1\alpha_2}=hq+a_1d_2s,
\]

with analogous second-row expressions. Blow up the smooth non-coordinate center

\[
Z=(\alpha_1,\alpha_2,d_1,d_2,p,q,r,s,h)=0
\]

at a generic real point with \(a_1b_2=-1\). Its exceptional divisor \(E_Z\) has

\[
v(\alpha_1)=v(\alpha_2)=v(d_1)=v(d_2)=v(p)=v(q)=v(r)=v(s)=v(h)=1,
\]

while \(v(a_1)=v(b_2)=0\). No weight on the original chart can realize simultaneously

\[
v(a_1)=v(b_2)=0,\qquad v(1+a_1b_2)=1.
\]

Thus it is absent from the LP. Here \(v(I)=4\); since the center has codimension \(9\) and the chart Jacobian is \(\alpha_1^3\alpha_2^3\),

\[
A_{E_Z}=9+6=15,\qquad 2\rho(E_Z)=\frac{15}{4}.
\]

This is not an undershoot, but it proves the family is genuinely unsearched.

**Inference.** Your result should be stated as

\[
\min_{\substack{\text{toroidal divisors over}\\
\text{the searched charts, generic centers}}}2\rho\geq\minAdm,
\]

not as a statement about all divisors over those charts.

**Concrete test.** Add \(h\) as a local coordinate on \(a_1\neq0\),

\[
b_2=\frac{h-1}{a_1},
\]

compose the exact Jacobian, and rerun the LP. Then recursively inspect common-zero components of the weighted initial ideal, rather than only coordinate centers.

## Q2. Does the normal-crossing folklore hold?

**Established fact.** Yes, under the full hypothesis that the ideal has been principalized:

\[
I\mathcal O_Y=\mathcal O_Y\!\left(-\sum_i N_iE_i\right),
\]

with the total divisor SNC. If a smooth center \(C\) of codimension \(c\) lies in precisely the components \(E_i\), \(i\in S\), then its blow-up produces \(F\) with

\[
N_F=\sum_{i\in S}N_i,\qquad
A_F=\sum_{i\in S}A_i+c-|S|.
\]

Consequently,

\[
\frac{A_F}{N_F}
=
\frac{\sum_{i\in S}N_i(A_i/N_i)+c-|S|}
     {\sum_{i\in S}N_i}
\geq \min_{i\in S}\frac{A_i}{N_i}.
\]

There are no exceptions after a genuine log resolution.

**Not applicable when:** the weak transform still has a residual ideal of order \(m>0\). Then

\[
N_F=\sum N_i+m,
\]

and the extra denominator can lower the ratio. An SNC zero-set is also insufficient: the ideal itself must be locally principal monomial.

**Inference here.** Your displayed \((2,2,2)\) leaf looks binomial but its ideal is already monomial after changing generators; see Q4. The \(L=3\) angular locus \(1+a_1b_2=0\), however, is not covered by that argument.

**Concrete test.** Verify either:

1. a monomial generating set for the transformed ideal, or  
2. a completed principalization with recorded \((A_i,N_i)\).

Do not infer NC from the displayed support alone.

## Q3. What is the first \(L\geq3\) hiding place?

**Established fact.** Generic intersections of rank strata may be exposed by enough pivot charts. What a layerwise toroidal peel misses is a special incidence relation among the angular data of adjacent pivots.

For \((2,2,2,2)\), the first relation is

\[
h=1+a_1b_2=0.
\]

It says that the rank-one row direction selected in \(C^{(1)}\) annihilates the rank-one column direction selected in \(C^{(2)}\).

For \((2,3,2,2)\), the corresponding shared-layer relation is

\[
h=1+a_{11}b_{21}+a_{12}b_{22}=0.
\]

These are non-coordinate hypersurfaces in the exceptional angular variables. Centers combining \(h=0\) with residual-block conditions \(D_{ijk}=0\) produce divisors not represented by the current LP.

**Inference.** The first plausible hiding place is not “a deeper rank stratum” by itself. It is a non-toroidal component or singular intersection of the weighted initial scheme on that stratum—especially one where all currently minimal product entries vanish simultaneously.

**Concrete test.** For both \(L=3\) instances:

1. introduce \(h\) as a coordinate on each open set where one coefficient is invertible;
2. substitute exactly and recompute the Jacobian;
3. blow centers \(h=0\) together with the relevant residual \(D\)-block and minimal product entries;
4. rerun the exact all-weights calculation.

## Q4. Can generic binomials cancel along a divisor?

**Established fact.** Yes. Generic coefficients do not prevent valuation-theoretic cancellation when the two terms have equal value.

For \(q=bg+\delta c\), blow up the origin of \(\mathbb A^4\), using

\[
b=t,\quad g=tu,\quad \delta=tv,\quad c=tz.
\]

Then

\[
q=t^2(u+vz).
\]

At the real point \(u=v=1,z=-1\), blow up the codimension-two center

\[
(t,u+vz)=0.
\]

The new divisor satisfies

\[
v(b)=v(g)=v(\delta)=v(c)=1,\qquad v(q)=3>2.
\]

Thus expanded monomial support is cancellation-correct only for monomial valuations with generic residue center.

**But your \((2,2,2)\) leaf is safe.** Its transformed ideal is

\[
\alpha\langle
g_0,g_1,\,
bg_0+\delta c_{210},\,
bg_1+\delta c_{211}
\rangle
=
\alpha\langle
g_0,g_1,\delta c_{210},\delta c_{211}
\rangle.
\]

So cancellation in either binomial cannot increase \(v(I)\): the ideal has an exact monomial generating set. Blowing up \((b,\delta)\) does not address cancellation and is toroidal anyway.

**Concrete test.** For every weight \(w\), compute the full weighted initial ideal \(\operatorname{in}_w(I)\), saturate by irrelevant/chart-denominator ideals, and decompose it. For each real irreducible component \(Z\) on the exceptional divisor, blow up \(Z\) and recompute the exact transformed generators. Testing individual generator supports is insufficient.

## Q5. Sharpest decorrelated exact check

**Recommendation.** Compute the local generalized Bernstein–Sato polynomial—or equivalently the local multiplier-ideal log canonical threshold—of the ideal \(I\) over \(\mathbb Q\), using Macaulay2’s `MultiplierIdeals`/`Dmodules` machinery.

Compute the lct of the four-entry ideal itself, not of \(\sum P_{ij}^2\), and localize at the origin. In standard algebraic conventions compare

\[
\operatorname{lct}_0(I)
\]

with \(3\) for \((2,2,2,2)\) and \(4\) for \((2,3,2,2)\); your \(2\rho\) is \(A/v(I)\).

This is complete and independent of the incidence resolution. Integral closure alone is not: lct is invariant under integral closure, but normalized-blow-up/Rees divisors need not contain every divisor computing lct. A specific weighted blow-up is an exact refutation tool but cannot corroborate completeness.

If the D-module computation finds a lower complex threshold, extract its center and verify that it has a real smooth point before treating it as a real counterexample.