## Q_A — GAP

- [DERIVED] The stated normal-crossings inference is not automatic. If
  \[
  \mathrm{loss}\asymp U\prod_i |u_i|^{2m_i},\qquad
  d\mu\asymp V\prod_i |u_i|^{p_i}\,du,
  \]
  then convergence requires
  \[
  c'<\min_i\frac{p_i+1}{2m_i},
  \]
  not \(\frac12\sum_i(p_i+1)\). The sum arises only after sector blow-ups create a joint outer divisor.

- [DERIVED] For the intended \((4,3,4)\) charge blocks, a successful sector such as
  \[
  r_1=r_0\tau_1,\qquad r_2=r_0\tau_2
  \]
  changes the measure to
  \[
  r_0^{10}\tau_1^2\tau_2^3\,dr_0\,d\tau_1\,d\tau_2
  \]
  and the loss to \(r_0^2(1+\tau_1^2+\tau_2^2)\), giving \(c'<11/2\). Leaving the three divisors independent would instead give the erroneous minimum \(3/2\).

- [DERIVED] There is a concrete chart where the naïve front-\(t=2\) unit fails. Blow up the \(2\times2\) Schur block as
  \[
  \Gamma
   =u\begin{pmatrix}1&s\\ t&st+v\end{pmatrix},
  \qquad |d\Gamma|=|u|^3\,du\,ds\,dt\,dv.
  \]
  Writing the rows of \(Q_b\) as \(q_1,q_2\), a bounded row operation gives
  \[
  |\Gamma Q_b|^2\asymp
  u^2\bigl(|q_1+s q_2|^2+v^2|q_2|^2\bigr).
  \]
  At \(v=0\), the coefficient of the second row vanishes. Thus the claimed lower-bounded unit on the front \(t=2\) chart does not exist.

- [DERIVED] This is the overlap with the rank-three front stratum:
  \[
  \begin{array}{c|ccccc}
  t&0&1&2&3&4\\ \hline
  (4-t)^2+\minAdm(t,4,4)&16&13&11&11&12 .
  \end{array}
  \]
  Hence the rank-one angular branch \(v=0\) is another binding branch, \(t=3\), not a worse-than-\(11/2\) branch.

- [INFERRED] A simultaneous refinement can still couple all radii and retain threshold \(11/2\), but F1 and F2 do not prove that the proposed sequential cover performs this refinement. The specific proof-failing chart is the \(u,v\) chart above; it is not yet a finiteness counterexample.

## Q_B — FATAL

- [ASSUMED] On a pivot chart where \(P^{-1}\) is bounded, triangular row operations make the loss comparable to
  \[
  R^2+|\Gamma Q_b|^2,\qquad R=|P Q_{\mathrm{tp}}|.
  \]

- [DERIVED] In the chart above, put
  \[
  H^2=|q_1+s q_2|^2+v^2|q_2|^2.
  \]
  Radial integration of the four-dimensional \(\Gamma\)-block gives, for \(c'>2\),
  \[
  \int_0^1u^3(R^2+u^2H^2)^{-c'}\,du
  \asymp
  \begin{cases}
  R^{-2c'},&H\lesssim R,\\[2mm]
  R^{4-2c'}H^{-4},&R\lesssim H.
  \end{cases}
  \]
  The second regime contains the residual weight \(H^{-4}\). It cannot be bounded by a constant times the plain reduced integrand
  \[
  R^{-2(c'-2)}.
  \]

- [DERIVED] At \(v=0\), \(H\) loses the \(q_2\)-direction altogether. Resolving that residual requires the deeper variables and the determinant-normal coordinate \(v\). Thus it cannot be discharged by a genuinely layer-local front peel.

- [DERIVED] Even the scalar model has
  \[
  \iint(R^2+\gamma^2y^2)^{-c'}\,d\gamma\,dy
  \asymp R^{1-2c'}\log(1/R)
  \]
  for \(c'>1/2\), rather than the exact plain shifted power. Bounded cutoffs prevent the false full-space determinant factor, but do not produce an exact plain handoff.

- [INFERRED] Therefore “one native peel followed immediately by plain hIH at exactly \(c'-ab/2\)” is false as stated. A repair needs either:

  - a decorated IH retaining truncated weights such as \(H^{-4}\); or
  - an equivalent simultaneous multi-level discharge lemma. After full discharge, logarithms could be absorbed using the strict slack and plain hIH at \(c'-ab/2+\varepsilon\), but that extra theorem is precisely what is currently missing.

## Q_C — GAP

- [DERIVED] The displayed \(\Gamma\)-chart is a clean bounded-box change of variables with Jacobian \(u^3\). Choosing each possible largest entry of \(\Gamma\) gives finitely many reciprocal charts with bounded \(s,t,v\).

- [DERIVED] No inverse determinant is needed near \(v=0\): one must retain \(v\) as an exceptional coordinate. Inverting \(v\) there would create exactly the uncontrolled determinant factor the bounded construction is meant to avoid.

- [INFERRED] The same principle applies to \(\operatorname{rank}Q_b=r<b\): choose a controlled \(r\)-minor only away from the lower-rank boundary; near that boundary, extract another radial/minor coordinate. The missing \(a(b-r)\) directions then appear as products of that coordinate with inactive \(\Gamma\)-directions.

- [INFERRED] Abstract semialgebraic principalization supplies finite measurable charts with monomial Jacobians. It does not by itself establish the advertised layer-by-layer \((S,J)\) formulas or their exponent table.

- [ASSUMED] The argument also needs pivot charts where \(P^{-1}\) is bounded, or else all powers arising from \(P^{-1}\) must be explicitly extracted. The setup does not state this chart hypothesis.

Thus there is no demonstrated intrinsic pivot obstruction, but the required explicit finite-cover CoV theorem remains unbuilt.

## Q_D — UNPROVEN

- [DERIVED] The most dangerous explicit branch found above does not lower the critical exponent. It changes from the binding \(t=2\) path
  \[
  4+3+4=11
  \]
  to the equally binding \(t=3\) branch
  \[
  1+\minAdm(3,4,4)=1+10=11.
  \]
  The full-rank angular branch gives \(12\), hence is safer.

- [INFERRED] Intersections of the two binding divisors are expected to increase logarithmic multiplicity at \(c'=11/2\), not lower the finiteness threshold below \(11/2\).

- [INFERRED] F1 shows that every rank-flag recursion path has total charge at least \(11\). What remains unproved is that every exceptional valuation of the coupled ideal is represented by such a rank flag.

- [INFERRED] I found no branch proving \(+\infty\) for any \(c'<11/2\). The evidence supports genuine finiteness, but the supplied facts do not certify it.

The single cheapest discriminating computation is to principalize, on the explicit rank-one angular chart,
\[
\mathcal I=(\,P Q_{\mathrm{tp}},\ u(q_1+s q_2),\ uvq_2\,),
\]
after inserting the two binding reduced-chain charts, and tabulate \((\operatorname{ord}_E\mathcal I,\operatorname{ord}_E\mathrm{Jac}+1)\) for every primitive toric ray. A ratio below \(11/2\) would be a genuine finiteness obstruction; ratios all at least \(11/2\) would identify the current problem as a construction/labour gap.

I found no genuine finiteness obstruction—only a fatal flaw in the literal plain-IH handoff and an unresolved finite-chart construction.