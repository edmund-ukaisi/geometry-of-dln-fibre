Overall verdict: **Route A is wrong as written.** The likely-correct route is the native bounded-box \((S,J)\) blow-up. Integrating Γ first and then trying to repair the emitted Gram determinant mixes two incompatible routes.

Risk ranking:

1. **Q5/Q2 — fatal:** the full-space Γ-atom destroys the bounded-domain cutoff.
2. **Q1 — major:** the general Jacobian equality is asserted, not derived; it holds only under a strong shared-divisor condition.
3. **Q3 — major:** the rank cover is set-theoretically finite but analytically incomplete.
4. **Q4 — unresolved:** the anchor works, but no general domination/coverage theorem is supplied.

## Q1 — general charges-ADD

**VERDICT: incomplete; the blanket equality is wrong.**

- **DERIVED:** For coupled radial blocks of dimensions \(q_1,\dots,q_k\), on a sector
  \(u_j=u_1\tau_j\), the polar Jacobians and the \(k-1\) coupling substitutions give
  \[
  \sum_j(q_j-1)+(k-1)=\sum_jq_j-1.
  \]
  Thus the anchor’s \(3+2+1=6\) is the \(k=2\) instance.

- **DERIVED:** If, additionally, every deeper charge is placed on that same divisor and
  \(\sum q_j=ab+\minAdm(\operatorname{redChain}_tM)\), then a binding cut gives the desired
  \(\minAdm(M)-1\).

- **DERIVED:** Those additional hypotheses are not consequences of the stated banked pieces. On a rank-\(r\) branch, Γ contributes only \(ar\), not \(ab\); the missing \(a(b-r)\) must come from rank-normal coordinates. On non-achieving deeper branches the total is \(Mval(T)>\minAdm(M)\), not exactly \(\minAdm(M)\).

- **INFERRED:** General \((S,J)\) charts have fresh divisors, reused divisors, and different generator supports. The correct obligation is a per-divisor terminal inequality involving its Jacobian exponent and its loss order, not “there is one \(u_0\) with exponent \(\minAdm-1\).”

**Cheapest check:** do the full pullback-Jacobian calculation for the first multi-run case, e.g. \((4,4,4,4)\) with charges \([4,3,4]\). Verify every Case-1/Case-2 chart, not merely that \(4+3+4=11\).

## Q2 — joint corner versus plain hIH

**VERDICT: wrong as written.**

- **DERIVED:** At a binding cut,
  \[
  c'-ab/2 \nearrow \tfrac12\minAdm(\operatorname{redChain}_tM).
  \]
  Hence plain hIH has zero slack for an additional Gram weight. Any Hölder split needs \(p>1\) while \(p(c'-ab/2)\) remains below the reduced threshold; this fails arbitrarily near the endpoint.

- **DERIVED:** Carrying the raw determinant into a decorated IH is not automatically enough: the full-space atom’s majorant can itself be nonintegrable even when the original bounded-Γ integral is finite.

- **INFERRED:** A one-peel handoff to plain hIH is possible only if the joint blow-up fully discharges the decoration while retaining the bounded Γ cutoff. That means applying the native decorated blow-up to the pre-atom integral. It cannot be obtained by resolving the post-atom residual \(R\).

Thus Step 3 and Step 4 describe two different architectures:

- post-atom: needs a cutoff-aware weighted/decorated theorem and may already have lost finiteness;
- native blow-up: keeps Γ, resolves jointly, and may eventually hand a plain shifted integral to hIH.

The repository itself records this distinction in [pure-vs-atom-adj.md](/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/genm-sjjoint-design/pure-vs-atom-adj.md).

## Q3 — finite chart cover

**VERDICT: set-theoretically sound, analytically incomplete.**

- **DERIVED:** There are finitely many ranks and finitely many minors, and every rank-\(r\) matrix has a nonzero \(r\times r\) minor. So a finite set cover exists.

- **DERIVED:** “Seams are null” does not solve the integral. Competing pivot charts overlap on positive-measure sets, while determinant-zero loci may be null only when the relevant determinant polynomial is nonzero. Under structural bottlenecks, full-rank loci may be empty.

- **DERIVED:** The divergence occurs in neighborhoods of the seam, not on the null seam itself. Splitting off the exact rank-deficient set leaves the same divergent punctured neighborhood.

- **DERIVED:** Permutations have Jacobian \(1\). Gaussian elimination using \(M^{-1}\) generally introduces powers of \(|\det M|^{-1}\); it does not have a uniformly controlled Jacobian as \(M\to\) singular.

- **INFERRED:** A valid rank-flag construction needs quantitative sectors, explicit tubular/blow-up coordinates, their Jacobians, and bounded overlap. “Recurse the rank flag” alone does not supply these.

**Cheapest check:** on a corank-one chart, write the exact coordinate map and its determinant. If any inverse minor appears without a radial variable compensating its power, the chart is unusable near the next rank drop.

## Q4 — joint-density faithfulness

**VERDICT: incomplete; the anchor is sound, the general claim is unproved.**

- **DERIVED:** A corner resolution dominates the joint-density estimate only after proving: finite proper chart coverage, exact pullback Jacobians, uniform comparison of the pulled-back loss, and bounded multiplicity.

- **DERIVED:** The chart \(u_1=u_0\tau\) covers only \(|u_1|\lesssim|u_0|\). Its reciprocal chart is required for \(|u_0|\lesssim|u_1|\), together with all pivot/angular charts.

- **DERIVED:** A finite logarithmic factor is harmless strictly below threshold:
  \[
  \int_0^\varepsilon r^\alpha \log^k(1/r)\,dr<\infty\quad(\alpha>-1).
  \]
  It is not harmless for pole multiplicity at the critical exponent.

- **INFERRED:** The claimed equivalence with the joint tube law is credible for the verified anchor but cannot be generalized from `radialStep` and support bookkeeping alone. The missing theorem is the actual chart-cover/change-of-variables statement.

**Cheapest check:** push both coupled sector charts forward and recover the ordered two-scale bound \(t_2^3t_3\log(e/t_2)\), with uniform constants.

## Q5 — fatal hole

**VERDICT: wrong. The fatal hole is the full-space Γ-atom majorant.**

A concrete binding example is
\[
M=(2,2,1,2),\qquad t=1,\qquad a=b=1,\qquad \minAdm(M)=2.
\]

- **DERIVED:** On a subbox where \(P\asymp1\) and \(Z\) is bounded away from zero, write the two rows of \(A'_1\) as \(y,\beta\) and set \(\alpha=Py+B\beta\). Then
  \[
  \mathrm{freedSchurLoss}
  \asymp \alpha^2+(\Gamma\beta)^2
  \]
  uniformly for bounded \(C\).

- **DERIVED:** At \(c'=3/4<\minAdm/2=1\), the bounded-box integral is finite: integrating \(\alpha\) produces \(|\Gamma\beta|^{-1/2}\), integrable in both Γ and \(\beta\).

- **DERIVED:** The full-space Γ-atom instead emits
  \[
  |\beta|^{-1}\,|\alpha|^{-1/2}.
  \]
  Its outer \(\beta\)-integral diverges logarithmically, even after removing the exact rank-zero point \(\beta=0\).

Therefore Step 2’s rank flag cannot repair Step 1, and Step 3 cannot make a genuinely nonintegrable majorant integrable by changing coordinates.

The design must choose the native bounded-box decorated blow-up before integrating Γ, or retain an explicit cutoff-aware crossover estimate. The advertised atom → Gram residual → joint corner → plain hIH chain does not prove \(I<\infty\).