### Q1 — Reachable

**Verdict — [INFERENCE] The wide regime is genuinely reachable.**

- [FACT] The induction hypothesis is invoked for every chain; it contains no ordering invariant such as \(M_2\le M_1\).
- [FACT] A nondegenerate binding cut supplies only \(a_\star,b_\star\ge1\). An off-sector with \(j\ge1\) is legitimate whenever the resulting \(a=a_\star-j\) and \(b=b_\star-j\) remain admissible.
- [FACT] In \((4,3,5,5)\), \(t_\star=1,j=1\) gives \(a_\star=3,b_\star=2\) and \(a=2,b=1\); nothing in the stated binding conditions involves \(M_2\) or forces \(a+b\le m\).
- [INFERENCE] Therefore binding-cut structure does not remove this shell. A proof relying on \(M_2\le M_1\) has a real generality gap.

### Q2 — Permutation invariance

**Verdict — [INFERENCE] Sorting is not a valid noncircular cover.**

- [FACT] Permutation invariance of the numerical threshold \(\minAdm\) does not imply equivalence of the underlying integrals.
- [FACT] Reordering widths generally changes both
  \[
  \sum_i M_iM_{i+1}
  \]
  and the dimensions of the matrix product. Hence there is no ordinary nonsingular, measure-preserving Euclidean change of variables intertwining the two integrands.
- [FACT] An abstract measure-space isomorphism between boxes of different dimensions would not preserve the matrix-product function and is irrelevant to change-of-variables arguments.
- [FACT] Chain reversal is an exceptional genuine symmetry, via transposition; arbitrary sorting is not.
- [INFERENCE] Finiteness may ultimately be permutation-invariant because the RLCT formula is, but using that fact here invokes essentially the theorem the recursion is meant to prove. Thus sorting is unavailable unless one supplies a separate analytic equivalence theorem.

### Q3 — Bound artifact and repair

**Verdict — [INFERENCE] There is no genuine divergence wall. The present divergence is an artifact, and direct \(Z_{\mathrm{deep}}\)-shelling is the right repair—but not a literal one-line substitution of \(\rho\) for \(m\).**

- [FACT] The externally known RLCT result makes the total nonnegative integral finite below the stated threshold.
- [FACT] By Tonelli/monotonicity, every measurable off-sector and their shell sum must then be finite.
- [INFERENCE] Consequently, an infinite corank majorant is merely vacuous. Ky–Fan/Weyl has under-certified the number of scale-controlled deep singular directions; it has not discovered an actual divergent subintegral.

- [FACT] For \(j\ge1\),
  \[
  \rho\ge a_\star+b_\star-1
       =a+b+2j-1
       \ge a+b+1.
  \]
  For a fixed \(Z_{\mathrm{deep}}\), this is more than the Wishart condition needed for \(W<\infty\).

- [FACT] On a given top-dimensional reduced component, its generic rank \(\rho\) is the ordinary matrix rank of \(Z_{\mathrm{deep}}\). The rank-drop set is a proper algebraic sublocus, so \(\operatorname{rank}Z_{\mathrm{deep}}=\rho\) almost everywhere with respect to that component’s intrinsic measure.
- [FACT] This is not the same as saying that the original full-product shell has \(\rho\) uniformly strong singular values. Near the rank-drop boundary, the relevant singular values can become arbitrarily small, and the constant in the Wishart estimate can blow up.
- [INFERENCE] Thus one cannot simply replace the Ky–Fan floor \(m\) by \(\rho\) inside the existing full-product-shell bound.

The required re-plumbing is:

1. [INFERENCE] Refine the decomposition using singular-value/rank shells of \(Z_{\mathrm{deep}}\) itself.
2. [INFERENCE] On generic co-minimizing component shells, use \(\rho\ge a+b+1\) in the Wishart integral.
3. [INFERENCE] Send neighborhoods of rank-drop loci to lower-\(\rho\) shells and retain their transverse volume/codimension rather than discarding it during decoupling.
4. [INFERENCE] Apply the recursive estimate/RLCT-additivity to show that the extra codimension outweighs the worsened corank factor.

- [FACT] Exact low-rank loci may have \(W=\infty\) pointwise while remaining measure-zero; that alone is harmless. What must be controlled quantitatively is the blow-up in their neighborhoods.
- [INFERENCE] The residual closes if every shell with zero summability slack would constitute a front-peel co-minimizer. The banked theorem then excludes such a shell with \(r<a+b\), while strict \(c'<\frac12\minAdm\) supplies positive slack for all remaining strata.
- [INFERENCE] Under that standard stratified-additivity lemma, this is principally a reorganization of banked combinatorics and Wishart estimates, not new geometry. Without the lemma, the banked generic-rank statement alone is insufficient—but the residual is a proof obligation, not an actual divergence wall.

**Most likely way this analysis is wrong — [INFERENCE]** “Every co-minimizer” may cover only top-dimensional reduced components, while a lower-dimensional rank-drop valuation could become critical only after adding the Wishart fibre loss. If so, that valuation would not be covered by the banked theorem, and an extended rank-stratified combinatorial/analytic lemma would be genuinely necessary.