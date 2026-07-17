**Q1.** [proof-sketch you can defend] For each leaf \(\ell\), add: a bounded measurable source \(U_\ell\subset\mathbb R^N\); a map \(\phi_\ell:U_\ell\to\mathbb R^N\); its target \(V_\ell=\phi_\ell(U_\ell)\); divisor coordinates \(x_{\ell i}\), orders \(a_{\ell i},b_{\ell i}\in\mathbb N\); residual \(R_\ell\ge0\); bounded factors \(u_{F,\ell},u_{J,\ell}\); and a change-of-variables certificate for \(\phi_\ell\) off null exceptional sets. Require an open \(O\supset Z(F)\cap[-1,1]^N\) with \(O\cap[-1,1]^N\subseteq\bigcup_\ell V_\ell\). The two identities are, for every \(y\in U_\ell\) in the first and almost every differentiability point in the second,
\[
 F(\phi_\ell(y))
 =u_{F,\ell}(y)\prod_i|x_{\ell i}(y)|^{2a_{\ell i}}R_\ell(y),
 \qquad
 |\det D\phi_\ell(y)|
 =u_{J,\ell}(y)\prod_i|x_{\ell i}(y)|^{b_{\ell i}},
\]
with constants \(0<m_F\le u_{F,\ell}\le M_F<\infty\) and \(0<m_J\le u_{J,\ell}\le M_J<\infty\) throughout \(U_\ell\). The CoV certificate may minimally say that every nonnegative measurable \(g\) satisfies \(\int_{V_\ell}g\le\int_{U_\ell}g\circ\phi_\ell\,|\det D\phi_\ell|\); equality needs a.e. multiplicity one.

**Q2.** [proof-sketch you can defend] The leaf integrand must be
\[
u_{J,\ell}u_{F,\ell}^{-c'}
 \prod_i|x_{\ell i}|^{\,b_{\ell i}-2c'a_{\ell i}}
 R_\ell^{-c'}.
\]
For a bounded unit residual, impose \(0<m_R\le R_\ell\le M_R\), contributing no threshold. For a Morse residual, a rank field alone is insufficient: require coordinates \(y=(x,z,w)\), with the divisor variables \(x\) disjoint from \(z\in\mathbb R^{\rho_\ell}\), and uniform bounds \(m_R\|z\|^2\le R_\ell(x,z,w)\le M_R\|z\|^2\). Then
\[
c'<\min\left(\min_{a_{\ell i}>0}\frac{b_{\ell i}+1}{2a_{\ell i}},\frac{\rho_\ell}{2}\right).
\]
[heuristic/inference] Resolving the Morse core further is unnecessary and would introduce more non-unit-Jacobian CoV obligations; the banked radial result is the cleaner endpoint.

**Q3.** [proof-sketch you can defend] Choose **(b), the RLCT route**, because the weighted-threshold transport already supplies the difficult chart transport. The load-bearing missing lemma is the **homogeneous local-to-box bridge**: if \(F(\lambda C)=\lambda^{2L}F(C)\) and \(K=[-1,1]^N\), then for every \(\varepsilon>0\),
\[
\int_{\varepsilon K}F^{-c'}=\varepsilon^{N-2Lc'}\int_KF^{-c'},
\]
so finiteness on any neighborhood of the origin implies finiteness on \(K\). This, together with finite chart gluing and boundedness away from \(Z(F)\), turns the transported local threshold into the desired box-integral statement.

**Q4.** [proof-sketch you can defend] No new combinatorial tree invariant is forced, but the analytic resolution bundle must contain—or derive—the source/image localization, image-cover theorem, CoV certificate, and residual normal-form certificate; a chart map plus the two scalar identities does not imply these. The sharpest failure mode is retaining coverage by abstract `chartDom` instead of coverage by the actual images \(\phi_\ell(U_\ell)\). The smallest supplied counterexample is \(M=(2,2,2)\): an abstract all-universe atlas passes the old cover and exponent tests at \(c'=8/5\), while the genuine binding charts have threshold \(3/2\), and the box integral diverges.