**1. Standard Theorem**

Yes. For a real analytic/algebraic germ \(F\), a single log resolution \(\pi:Y\to X\) gives local charts with

\[
F\circ \pi = U(y)\prod_i y_i^{N_i}, \qquad |\det D\pi|=V(y)\prod_i |y_i|^{\nu_i-1},
\]

where \(U,V\) are nonvanishing units. Then

\[
\int |F|^{-c} < \infty
\]

is reduced chartwise to monomial integrals

\[
\int \prod_i |y_i|^{\nu_i-1-cN_i}\,dy,
\]

so convergence holds exactly when \(c<\min_i \nu_i/N_i\), and divergence at/above the minimum is witnessed on a chart containing a divisor attaining that minimum. Saito states the Hironaka normal-crossing form and the formula \(\operatorname{rlct}(f)=\min_j (a_j+1)/m_j\). ([arxiv.org](https://arxiv.org/pdf/0707.2308))

**2. The `a=0` Shear Singularity**

Yes, provided the “upper-bound cover” is a genuine resolved atlas, not merely the generic \(a\neq0\) Schur chart. The failed `phi334` degenerates because it tries to pass through the blow-up center while using coordinates valid only when \(a\) is invertible. The expression \(a^{-1}bS\) is not analytic at \(a=0\); if one forces a limiting relation by hand, one typically loses the ratio/direction variables. That is exactly why the Jacobian drops rank and the image becomes null.

The blow-up cures this by replacing the center with exceptional-direction coordinates. In a chart where

\[
a = u\hat a,\qquad b=u\hat b,\qquad \text{normal coordinates}=u(\text{direction variables}),
\]

the singular term becomes

\[
a^{-1}bS = (u\hat a)^{-1}(u\hat b)S=\hat a^{-1}\hat bS,
\]

on the subchart where \(\hat a\) is invertible. The map has Jacobian \(\sim u^{\#\mathrm{active}-1}\), hence is a local diffeomorphism off \(u=0\). The exceptional divisor \(u=0\) is where the determinant vanishes, but that is normal for a blow-up; change of variables is applied on \(u\neq0\), and divergence is read as \(u\to0\).

Caveat: if the achiever direction has \(\hat a\) singular in that chart, then this particular chart is not the right one. The full resolution must include the adjacent pivot/blow-up charts or further blow-ups. A generic-\(a\) cover alone would not supply the lower-bound chart.

**3. Shared Vs Separate**

Shared hardest atom:

\[
F\circ\phi = u^2 U,\qquad |\det D\phi|=|u|^{Mval-1}\cdot V,
\]

with \(U,V\) bounded above and below away from \(0\), plus the honest local measure change-of-variables. This is the main analytic construction both sides need.

Lower bound additionally needs only:

- choose an admissible minimizer \(T\) with \(Mval(T)=minAdm\);
- choose the real resolved chart/leaf over that minimizer;
- restrict to a positive-measure slice where all nonbinding variables and units are controlled;
- prove

\[
\int_0^\delta |u|^{Mval-1-2c'}\,du=\infty
\]

for \(c'\ge Mval/2=minAdm/2\), inside every small cube.

Upper bound additionally needs:

- the finite chart family covering a neighborhood up to null sets;
- every chart’s exponent data;
- the combinatorial inequality \(Mval(T)\ge minAdm\) for every emitted divisor/profile;
- summability of the finite sum of monomial chart integrals for every \(c'<minAdm/2\).

So yes: the honest per-node blow-up chart with CoV is the shared hard atom. The upper leg has more global coverage/combinatorial bookkeeping; the lower leg has the binding-leaf and positive-measure divergence bookkeeping.

**4. Net Verdict**

One coupled normal-crossings resolution should serve both bounds. The standard theorem says it does, and in this architecture the `a=0` failure is not evidence that lower needs a different construction; it is evidence that the lower proof tried to use an unresolved, non-diffeomorphic chart. The efficient Lean shape is therefore: build the coupled resolution atlas once, with honest Schur/blow-up charts and Jacobians, then expose two consumers: `hfin` over all charts and `hdiv` on a minimizing chart. This reduces total work versus two independent constructions, but only if the “upper cover” is truly the full resolved atlas; a generic-shear or null-center shortcut would not contain the lower witness.