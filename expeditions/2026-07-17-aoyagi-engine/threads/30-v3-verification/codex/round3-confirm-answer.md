Audited exact commit `f8db23000`.

## 1. D1 dom-wide certificates — CONFIRMED-FIXED

- [VERIFIED] For \(g(s,t)=(s(1-s),st)\), `hdom_sub` places \((1,0)\) in `nbhd`. With dominant monomial \(b=s\), `hideal_bwd` would give
  \[
  1=b(1,0)=\sum_i a_i(1,0)(F_i\circ g)(1,0)=0.
  \]
  Thus [hideal_bwd](/tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean:111) fails. Independently, [hg_inj](/tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean:85) fails because the branches near \(s=0\) and \(s=1\) collide on open sets; a null `excep` cannot remove one branch.

- [VERIFIED] For \(g_B(u,v)=(v(u-2),v)\), the germ monomial is \(b=v\). A reverse representation would imply, for \(v\ne0\),
  \[
  1=A(u,v)(u-2)+B(u,v)v.
  \]
  Continuity at \((2,0)\in\mathrm{dom}\subseteq\mathrm{nbhd}\) gives \(1=0\). Hence its dom-wide `hideal_bwd` is impossible.

- [VERIFIED] The two-chart blow-up remains inhabitable:
  \[
  g_1(u,v)=(u,uv),\qquad g_2(u,v)=(uv,v).
  \]
  Take `nbhd = univ`, exceptional sets \(\{u=0\}\), \(\{v=0\}\), units \(1\), Jacobian exponents \((1,0)\), \((0,1)\), and dominant monomials \(u,v\). The global ideal representations are respectively
  \[
  (u,uv)=u(1,v),\qquad (uv,v)=v(u,1),
  \]
  with reverse coefficients \((1,0)\), \((0,1)\). Compact boxes
  \[
  [-\varepsilon,\varepsilon]\times[-1,1],\quad
  [-1,1]\times[-\varepsilon,\varepsilon]
  \]
  cover \(U=(-\varepsilon,\varepsilon)^2\).

- [INFERRED] A fresh remote-branch attack found no replacement counterexample to `rlctAt_sumSqFam_eq_iInf_charts`. If \(p\in\mathrm{dom}\) lies over \(x_0\), dom-wide ideal equality forces the dominant monomial to vanish at \(p\). Its active coordinate axes at \(p\) are a subset of those active at the chart origin, so the origin’s monomial threshold is no larger than the threshold at \(p\). Compactness, finite covering, and a.e. injectivity then supply the expected CoV argument. The theorem remains a `sorry`, so this is statement-level confirmation, not Lean verification.

## 2. D2 injectivity — CONFIRMED-FIXED

[INFERRED] `InjOn g (nbhd \ excep)` with `volume excep = 0` is sufficient. Analyticity makes \(g\) locally Lipschitz on the relevant compact domains, so \(g(\mathrm{excep}\cap\mathrm{dom})\) is null. Consequently the area-formula multiplicity satisfies \(N_c(w)\le1\) a.e. per chart, and \(N(w)\le\text{numCharts}\) across the finite atlas. Thus downstairs integrability transports upstairs, equivalently upstairs divergence transports downstairs.

## 3. Weighted guards / deletion — CONFIRMED-FIXED

[VERIFIED] The deletion of `LocallyNullZerosW` is sound. From \(K_G\le C K_F\), off the null set \(\{K_G=0\}\),
\[
0\le W K_F^{-c}\le C^c W K_G^{-c}.
\]
At every point where \(W=0\), both sides are exactly zero. Hence positive-measure zeros of \(W\) cannot reverse the comparison; they only remove mass. The reverse representation gives the symmetric inequality for equality.

The added measurability hypotheses in [the weighted lemmas](/tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/IdealInvariance.lean:204) reject the previous Vitali-modulated family. Both \(K\)-zero guards remain in the two-sided statement.

## 4. \(e(0)\)/homeomorphism — NEW-KILL

[VERIFIED] The two old examples are rejected:

- Translation fails `he0 : e 0 = 0`.
- The discontinuous measure-preserving bijection is not a `≃ₜ`.
- [coreReduction](/tmp/aoyagi-v3-review/lean/DLNFibre/DLN/Aoyagi/LearningCoefficient.lean:70) still requires both `MeasurePreserving e` and `e 0 = 0`.

However, [exists_coreResolution](/tmp/aoyagi-v3-review/lean/DLNFibre/DLN/Aoyagi/LearningCoefficient.lean:88) quantifies over every origin-fixing homeomorphism, without requiring the linear/analytic flatten.

Take \(N=1\), \(d=(1,1)\), identify both spaces with \(\mathbb R\), and set
\[
e(u)=u|u|.
\]
This is an origin-fixing homeomorphism with inverse
\(\operatorname{sgn}(v)\sqrt{|v|}\). The other hypotheses hold, and `qipFeasible` contains the function \(a(0)=1\). Here
\[
\operatorname{coreGen}(u)=u|u|.
\]

Any chart has one source coordinate. `hbind` and `hunit_mult` force its dominant monomial to be \(u\). Then dom-wide `hideal_bwd` supplies a continuous \(a\) with
\[
u=a(u)\,g(u)|g(u)|.
\]
Since \(g\) is analytic and \(g(0)=0\), locally \(|g(u)|\le L|u|\); continuity bounds \(|a(u)|\le A\). Therefore
\[
|u|\le AL^2|u|^2,
\qquad\text{so}\qquad
1\le AL^2|u|,
\]
which is impossible as \(u\to0\). Thus no `Chart`, hence no `Resolution`, exists.

## OVERALL — NO

v4.1 does not clear the “no false frontier statements” bar.

Ranked kill:

1. [VERIFIED] `exists_coreResolution` is false for arbitrary origin-fixing homeomorphisms. It must restrict `e` to the actual linear/analytic coordinate flatten—or jointly existentially produce that flatten and its resolution.