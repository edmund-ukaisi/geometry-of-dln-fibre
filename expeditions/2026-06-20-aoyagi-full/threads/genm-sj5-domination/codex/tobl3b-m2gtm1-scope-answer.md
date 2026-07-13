Bottom line: **Q1 yes, the wide regime is reachable; Q2 no, codimension permutation-invariance is not an analytic cover; Q3 yes, any claimed divergence below the threshold is a bound artifact, though exact-rank stratification alone is insufficient.**

## Preliminary analytic checks

- **[FACT]** For fixed \(Z\) of rank \(r\), after an SVD and invertible linear changes in the active columns, \(W\) has the same local integrability as
  \[
  \int_{C\in\mathbb R^{b\times r}_{\mathrm{bounded}}}
  \det(CC^{T})^{-a/2}\,dC.
  \]

- **[FACT]** The real Wishart/matrix-gamma convergence condition is
  \[
  \frac a2<\frac{r-b+1}{2},
  \qquad\text{i.e.}\qquad a<r-b+1.
  \]
  For integers \(a,b,r\) with \(a,b\ge1\), this is exactly
  \[
  r\ge a+b.
  \]
  Equality \(r=a+b-1\) is logarithmically divergent. If \(r<b\), the Gram determinant vanishes identically.

- **[INFERENCE]** Therefore the stated fixed-\(Z\) criterion
  \[
  W(Z)<\infty\iff \operatorname{rank}Z\ge a+b
  \]
  is correct.

- **[FACT]** If \(Z_{\rm full}=BZ_{\rm deep}\), then
  \[
  \operatorname{rank}(Z_{\rm full})\le \operatorname{rank}(Z_{\rm deep}),
  \qquad
  \sigma_k(BZ_{\rm deep})\le \|B\|_{\rm op}\sigma_k(Z_{\rm deep}).
  \]
  Thus, if the shell supplies \(q-j\) strong singular directions of \(Z_{\rm full}\), where \(q=\min(M_1,M_L)\), then it supplies at least
  \[
  m=q-j=\min(M_1,M_L)-j
  \]
  strong directions of \(Z_{\rm deep}\), up to a bounded threshold rescaling.

- **[FACT]** This conclusion requires a rank/strong-singular-value statement about \(Z_{\rm full}\). The rank of the multiplier \(B\) alone does not give it.

- **[INFERENCE]** The condition \(m\ge a+b\) is only a sufficient certificate for \(W<\infty\). The converse
  \[
  m<a+b\Longrightarrow W=\infty
  \]
  is false unless the shell also says the actual rank is exactly \(m\). The actual rank can exceed the certified floor.

- **[FACT]** There is also an indexing mismatch in the question: under the opening convention, \(A_1\cdots A_{L-1}\) has \(M_1\) rows. The later dimensions are consistent if \(Z_{\rm deep}=A_2\cdots A_{L-1}\) and \(Z_{\rm full}=A_1Z_{\rm deep}\), or after an equivalent post-peel relabeling.

## Q1 — Reachability

- **[INFERENCE — verdict]** Yes. A universally quantified front-peeling step must handle wide chains \(M_2>M_1\), and binding-cut minimality does not imply \(M_2\le M_1\) or \(m\ge a+b\).

- **[FACT]** The recursion minimizes over every
  \[
  0\le t\le\min(M_0,M_1).
  \]
  Neither the legal-cut condition nor the binding equality compares \(M_2\) with \(M_1\).

- **[FACT]** There are genuine unique-positive-binding examples. For
  \[
  M=(4,3,5,6),
  \]
  the four cut values are
  \[
  12,\ 11,\ 12,\ 14.
  \]
  Hence \(u_\star=1\) is the unique binding cut. On the off-sector \(u=2\),
  \[
  j=1,\qquad a=4-2=2,\qquad b=3-2=1,
  \]
  while
  \[
  m=\min(3,6)-1=2<3=a+b.
  \]

- **[INFERENCE]** Thus no rule excluding \(u_\star=0\), no tie-breaking convention, and no choice of another minimizer removes the reachability problem.

- **[FACT]** The particular example in the question,
  \[
  M=(4,3,4,4),
  \]
  is not a binding-\(1\) example under the displayed recursion. Its cut values are
  \[
  12,\ 10,\ 9,\ 10,
  \]
  so its unique binding cut is \(u_\star=2\).

- **[INFERENCE]** The supplied witness is arithmetically incorrect, but the general reachability conclusion remains correct.

## Q2 — Permutation-invariance cover

- **[INFERENCE — verdict]** No. Permutation-invariance of \(\minAdm\) does not by itself transfer box-integral finiteness.

- **[FACT]** For the example,
  \[
  \dim\operatorname{Params}(4,3,4,4)=12+12+16=40,
  \]
  whereas
  \[
  \dim\operatorname{Params}(4,4,4,3)=16+16+12=44.
  \]
  Hence there is no analytic change of variables with a nonzero Jacobian between the two parameter spaces.

- **[FACT]** Hidden-layer base changes
  \[
  (A_{i-1},A_i)\mapsto(A_{i-1}G^{-1},GA_i)
  \]
  preserve the product only within a fixed width vector. They do not interchange unequal hidden dimensions and generally do not preserve the cube.

- **[FACT]** Reversal is a genuine exception: transposing every matrix and reversing the order gives an exact box-preserving equivalence between \(M\) and \((M_L,\ldots,M_0)\). Arbitrary permutations do not arise this way.

- **[FACT]** F1 has the wrong direction for this purpose:
  \[
  \operatorname{rlct}\le \tfrac12\minAdm
  \]
  does not prove finiteness below \(\tfrac12\minAdm\).

- **[INFERENCE]** Combining permutation-invariance of \(\minAdm\) with F2 would prove equal thresholds, but that uses precisely the Aoyagi equality the recursion is meant to replace. It is circular for this project.

- **[INFERENCE]** A separate analytic “adjacent-width swap” theorem could conceivably establish permutation-invariance directly, but that would be a substantial new theorem, not a consequence of combinatorial invariance or a routine base change.

## Q3 — Artifact or genuine wall?

- **[INFERENCE — verdict]** Given the stated F2 consequence and the assumption that the shell is a measurable restriction of the original integral, a true divergent shell below the threshold is impossible. The failure is necessarily in the bound or in what the shell floor certifies.

- **[FACT]** For a nonnegative integrand and measurable shell \(S\),
  \[
  \int_S \mathrm{loss}^{-c'}\le
  \int_{\mathrm{box}}\mathrm{loss}^{-c'}<\infty.
  \]

- **[FACT]** This does not force every conditional slice to be finite. A conditional integral may equal \(+\infty\) on a measure-zero rank-deficient tail stratum without making the total integral infinite.

- **[FACT]** Nor does it force a lossy majorant such as \(W\) to be finite: enlarging domains or dropping positive energy terms may turn a finite true contribution into an infinite comparator.

- **[INFERENCE]** In the wide examples, \(m<a+b\) primarily says “the coarse shell information is insufficient.” It does not establish that the actual \(Z_{\rm deep}\) has rank \(m\).

- **[FACT]** For a multi-layer tail, the generic rank is
  \[
  \min(M_2,M_3,\ldots,M_L),
  \]
  not merely \(\min(M_2,M_L)\). The endpoint formula is correct only when no narrower intermediate layer intervenes.

- **[INFERENCE]** A finer strategy can work in principle, but exact-rank strata alone are too coarse. It needs:

  - **[FACT]** Quantitative singular-value shells, for example according to how many singular values lie below a dyadic scale \(\varepsilon\). Exact rank loci do not control blow-up in their neighborhoods.

  - **[FACT]** On a shell with \(\rho\) uniformly strong directions and \(\rho\ge a+b\), a Wishart/Loewner comparison gives a uniform bound, with an explicit negative power of \(\varepsilon\).

  - **[FACT]** When \(\rho<a+b\), the same \(W\) genuinely diverges. One must retain previously discarded loss terms or re-peel at a deeper cut, reducing the corank block rather than continuing with the identical comparator.

  - **[INFERENCE]** For \(u=u_\star+j\), the natural recursive budget is
    \[
    (M_0-u)(M_1-u)+\minAdm(\operatorname{redChain}(u,M))
    \ge \minAdm(M),
    \]
    which follows directly from cut soundness. This is the codimension/exponent balance needed for the reduced-chain induction.

  - **[FACT]** The low-rank locus has positive determinantal codimension in free matrix space, but its preimage under the tail-product map need not have that naive codimension. Its tubular-volume estimate must be proved using the tail recursion or resolution of singularities.

  - **[INFERENCE]** After resolving those tail strata, normal-crossing/RLCT additivity combines the Jacobian codimension gain with the corank-weight exponent. Strictness \(c'<\frac12\minAdm(M)\) should make the resulting dyadic series summable; equality cases may require interpolation to control logarithms.

- **[INFERENCE]** Thus there is no genuine “wall” for the true shell. There is a wall for the coarse proof that replaces actual tail rank by the floor \(m\) and then demands pointwise Wishart convergence uniformly on the entire shell.

**[INFERENCE — most likely failure mode of this analysis]** The most likely error is that the project’s post-peel variables \(j,Z_{\rm full},Z_{\rm deep}\) encode a stronger exact singular-value condition than the literal setup states; such an omitted invariant could invalidate my reachability witness or turn \(m\) from a mere floor into an exact shell rank.