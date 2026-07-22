## Q1. A single pinned pivot does not cover a neighbourhood

**Verdict:** If \(|S|\ge 2\), pinning \(p=\operatorname{canonPivot}\) cannot give a set-theoretic neighbourhood cover. With compact chart boxes, it misses an open, positive-measure sector—not merely a null set.

For the unrestricted map \(B_{S,p}\),

\[
\operatorname{im} B_{S,p}
=
\{x:x_p\neq 0\}
\;\cup\;
\{x:x_j=0\text{ for every }j\in S\}.
\]

Indeed, when \(x_p\neq0\),

\[
w_p=x_p,\qquad w_j=x_j/x_p\quad(j\in S\setminus\{p\}),
\]

while \(x_p=0\) forces the entire \(S\)-block of the image to vanish. Hence the unavoidable escape set is

\[
E_p=\{x:x_p=0,\ (x_j)_{j\in S\setminus\{p\}}\neq0\}.
\]

This has dimension \(D-1\), codimension \(1\), and Lebesgue measure zero. Since every path map has the root blow-up outermost,

\[
\operatorname{im}(g_P)\subseteq \operatorname{im}(B_{S_{\rm root},p_{\rm root}}),
\]

so every point of \(E_{p_{\rm root}}\) escapes every chart.

Compact sources make the failure stronger. Because there are finitely many paths and the inputs to the root \(B_{S,p}\) range over compact sets, there is an \(M<\infty\) such that every covered point satisfies

\[
|x_j|\le M|x_p|,\qquad j\in S\setminus\{p\}.
\]

Thus every ball around \(0\) contains the open positive-measure escape sector

\[
\{x:|x_j|>M|x_p|\}
\]

for any fixed \(j\neq p\). This is full-dimensional, hence “codimension \(0\)” in the usual informal sense.

A concrete witness is \(D=2\), \(S=\{1,2\}\), \(p=1\), identity shear. From a bounded box one has \(|x_2|\le M|x_1|\), so

\[
x=(\varepsilon^2,\varepsilon)
\]

escapes for all sufficiently small \(\varepsilon>0\).

The minimal cover-level change is

\[
p=\operatorname{canonPivot}(\text{state})
\quad\longrightarrow\quad
p\in \operatorname{canonCenter}(\text{state}),
\]

with one chart for every permitted pivot. All pivots are necessary: if \(r\in S\) is omitted, a point supported only on the \(r\)-axis lies in none of the selected blow-up images.

For \(|S|=1\), there is only one pivot and no problem.

This repairs coverage only. It does not automatically preserve the other chart invariants.

---

## Q2. What survives arbitrary-pivot fanning?

### L6: only part of it transfers automatically

For every \(p\in S\), the following are pivot-uniform facts:

- \(B_{S,p}\circ\phi\) is polynomial, hence analytic.
- It fixes the origin.
- It is injective wherever the actual input pivot \(\phi_p(w)\) is nonzero.
- The exceptional set \(\{\phi_p=0\}\) has measure zero.
- The fresh Jacobian vanishing order is always \(|S|-1\), independent of which \(p\) was chosen.

However, the claimed coordinate-monomial formula does **not** follow for arbitrary \(p\). Exactly,

\[
\det D(B_{S,p}\circ\phi)(w)
=
\phi_p(w)^{|S|-1},
\]

because \(\det D\phi=1\). This is a monomial in the source coordinate \(w_p\) only if the shear has the requisite compatibility with that pivot.

Concrete counterexample:

\[
S=\{1,2\},\qquad
\phi(w_1,w_2)=(w_1,w_2+w_1^2).
\]

This is an origin-fixing triangular polynomial automorphism with determinant \(1\). For the canonical pivot \(p=1\),

\[
\det D(B_{S,1}\circ\phi)=w_1,
\]

a coordinate monomial. For the fanned pivot \(p=2\),

\[
\det D(B_{S,2}\circ\phi)=w_2+w_1^2,
\]

which is not a monomial and whose exceptional hypersurface is not \(w_2=0\).

Therefore:

- Analyticity and origin-fixing transfer.
- A.e. injectivity transfers if the exceptional set is defined correctly using the intermediate pivot function \(\phi_p\).
- The coordinate-axis exceptional-set description and pure coordinate-monomial Jacobian do **not** transfer from the supplied facts.
- Consequently the full stated L6 does **not** survive the redesign without additional shear–pivot compatibility and a new composition proof.

### L8: the existential part survives; the universal part does not transfer

The numerical fresh contribution \(|S|-1\) is pivot-independent. Intrinsically, affine charts of the same blow-up describe the same exceptional divisor, so one may expect its discrepancy to be chart-independent.

But L8 is stated as a coordinate read-off on the chart’s binding axis. The new charts need not even have a Jacobian monomial on \(w_p\), as the example above shows. In that case “the exponent on the binding axis” is not defined in the required sense.

Hence:

- Every previously realised leaf exponent remains realised, because the canonical-pivot charts are still among the fanned charts.
- The assertion “every new chart satisfies the read-off formula” requires a new proof and is false under the stated assumptions in general.
- Even if stronger shear hypotheses restore L6, one must still prove that the new pivot axis represents the leaf divisor used by the combinatorial bookkeeping. No such assumption is given.

### Descent/FoldStepInv: it does not transfer

There are two independent failures.

First, after the fixed shear the actual exceptional equation is \(\phi_p(w)=0\), not necessarily \(w_p=0\). If the pullback under \(B_{S,p}\) contains the factor \(u_p^k\), then after precomposition by \(\phi\) the factor is

\[
\phi_p(w)^k,
\]

not \(w_p^k\).

Using the same shear as above and residual \(R(x)=x_2\):

- With canonical \(p=1\),

  \[
  R\circ B_{S,1}\circ\phi
  =w_1(w_2+w_1^2),
  \]

  so division by \(w_1\) is polynomial.

- With fanned \(p=2\),

  \[
  R\circ B_{S,2}\circ\phi
  =w_2+w_1^2,
  \]

  which is not divisible by \(w_2\).

Thus the stated strict transform may cease to be polynomial.

Second, the merge/case-1(1) pivot-separation argument plainly fails for a current-layer pivot. For the canonical birth corner \(b\), setting \(w_b=1\) does not evaluate any current-layer coordinate. If instead \(p=c\) belongs to the current layer, setting \(w_c=1\):

- deletes that current-layer variable;
- identifies monomials differing only in their \(c\)-degree;
- can cause support collapse or cancellation.

For example, \(w_c-w_c^2\) becomes \(0\) after \(w_c=1\), while setting a lower-layer variable \(w_b=1\) leaves its current-layer support unchanged.

So the merge proof does **not** survive. More strongly, FoldStepInv itself is not preserved by the proposed fanning from the information given. It would require a pivot-dependent strict-transform definition, updated divisor bookkeeping, and a new invariant proof.

---

## Q3. Fanning is needed at every nontrivial step

**Verdict:** For the general recursive argmax cover, every node with \(|S|\ge2\) must fan over all \(p\in S\). Root-only fanning is insufficient. Centers of size \(1\) need no fanning because their unique blow-up chart is the identity on that block.

At each inverse-routing stage, one chooses

\[
p\in\operatorname*{argmax}_{q\in S}|x_q|
\]

and sets \(u_j=x_j/x_p\). To guarantee \(|u_j|\le1\), that maximizing pivot must be available at that particular node. The same argument must then be repeated for the intermediate point at the next inner step.

A two-step witness shows that root-only fanning fails. Let \(D=2\), both centers be \(\{1,2\}\), all shears be the identity, fan the root pivot, but fix the inner pivot to \(1\). For \(|w_i|\le M\), the two root choices give

\[
B_1(B_1(w))=(w_1,w_1^2w_2),
\]

so \(|x_2|\le M|x_1|^2\), and

\[
B_2(B_1(w))=(w_1^2w_2,w_1w_2),
\]

so \(|x_1|\le M|x_2|\).

The points

\[
x=(t,t^{3/2})
\]

satisfy neither inequality for sufficiently small \(t>0\). Thus they escape despite complete root fanning.

In a particular oracle, overlaps or additional range restrictions could make some charts redundant. No such structure is given. Therefore fanning every non-singleton center is the minimal generally valid recursive design.

---

## Q4. Full coverage has no intrinsic tie or exceptional-locus obstruction

**Verdict:** With complete fanning and adequately chosen source boxes, the cover can be genuinely set-theoretic, with empty escape set.

- **Pivot ties:** Choose any maximizer. Every tied choice has ratios of modulus at most \(1\).
- **Pivot zero:** If a maximizing pivot is zero, then every coordinate in the center block is zero. Choose all slope coordinates to be zero; this maps to the desired block-zero point.
- **Whole block zero:** It is contained in every relevant chart image.
- **Shears:** Since \(\phi\) is a global bijection, after constructing the blow-up preimage \(u\), take \(w=\phi^{-1}(u)\). A shear creates no omitted set.

The only extra assumption needed concerns box sizes. A shear need not preserve the unit box. Nevertheless, argmax inversion produces bounded slope coordinates, and polynomial inverses send bounded sets to bounded sets. Because the tree is finite, all recursively routed preimages of a sufficiently small closed target cube lie in finitely many bounded sets, which can be enclosed in compact source boxes.

If the boxes are preassigned and too small, fanning alone does not guarantee coverage. Subject to choosing them large enough, ties, zero pivots, and shear hypersurfaces cause no residual escape.

Overall: pivot fanning repairs the atlas cover, but the proposed “keep the canonical shear and simply allow every pivot” redesign does **not** preserve the full L6/L8/Descent package. The merge invariant is the sharpest failure, not a harmless proof gap.