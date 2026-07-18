### Q1

Conditionally faithful, but several phrases are too strong.

A safer sentence is:

> §5 constructs an explicit chartwise log-principalization of the matrix-product ideal; integrability on each chart is controlled by discrepancy-to-vanishing-order ratios, and their minimum is reduced to a discrete quadratic optimization.

Load-bearing cautions:

- “Free regular directions” is wrong terminology. These are transverse regular generators, contributing \(q/2\); genuinely free parameters contribute \(0\).
- Diagonal monomial generators are not automatically a principalization. You need the divisibility/common-factor invariant, SNC divisors, and
  \[
  I\mathcal O=(u_1^{k_1}\cdots u_m^{k_m}),\qquad
  |\det D\pi|=\text{unit}\prod |u_j|^{h_j}.
  \]
- The ratio is \((h_j+1)/(2k_j)\). Your formula \(\frac12 M_{s,k}\) is valid only if \(M_{s,k}=h_j+1\) and \(k_j=1\) precisely for the listed \(\tilde t_{s,k}=0\) divisors. Calling \(M\) the “Jacobian exponent” loses the \(+1\): the exponent is \(M-1\).
- The cases may be recursive branches/stages involving several blow-ups, not literally the charts of one blow-up. That identification needs checking.
- Yes, omitted charts could produce a smaller ratio. Excluding this requires an exhaustive atlas of an actual proper log-principalization, or an equivalent direct covering/integrability proof.
- \(\theta\) does not count attaining charts. It is the maximal number of critical divisors meeting simultaneously with nonzero contribution.
- “The origin is worst” only justifies a global/minimum-over-the-fibre RLCT. It does not imply that every prescribed local true parameter has the origin’s RLCT.

### Q2

The inequality bookkeeping is decisive:

\[
\begin{array}{c|c|c}
\text{Claim} & \text{Meaning} & \text{Coverage needed?}\\
\hline
\lambda\ge C & \text{finite for every }c<C & \text{Yes}\\
\lambda\le C & \text{divergence at }c=C & \text{No: one chart/valuation suffices}
\end{array}
\]

Thus a full native equality contains Path A’s hard finiteness/coverage content. Path B cannot skip it unless the lower bound is obtained independently.

Your marginal list is roughly right if the upper bound is obtained from an attaining resolution chart, although B2 only needs a local punctured-chart change of variables, unit bounds, and positivity—not a full two-sided global birational theorem.

There may be a cheaper upper bound: if you prove that `minAdm` is the codimension of a smooth stratum contained in the zero set, then the standard estimate
\[
\lambda\le \tfrac12\operatorname{codim}
\]
gives \(\lambda\le\frac12\minAdm\) without B1–B3. That identification is essential; a generic codimension bound with the wrong codimension proves nothing sharp.

### Q3

For the whole native theorem, the hardest object is:

> an exhaustive proper log-principalization atlas, including the proof that every relevant region is covered and every pullback ideal/Jacobian has the asserted monomial form.

That is essentially (a), strengthened beyond mere termination.

For the marginal extension after Path A is genuinely completed, coverage is already paid for. The new hard object is then (b), but only its local one-chart divergence transport. If the sharp codimension argument works, the marginal hard object instead becomes proving `minAdm = codimension` and constructing the corresponding smooth stratum.