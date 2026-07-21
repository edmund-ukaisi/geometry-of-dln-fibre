## (1) Divisibility chain at full generality

**VERDICT: SOUND for positive widths.** No non-monotone-width counterexample breaks the \(b\)-chain.

Iterating

\[
b_0=1,\qquad
b_i=\left(\prod_{\widetilde t_{s,k}=i-1}u_{s,k}\right)b_{i-1}
\]

gives exactly

\[
b_i=\prod_{\widetilde t_{s,k}<i}u_{s,k}.
\]

Thus the supports are nested and \(b_i\mid b_{i+1}\).

The three step mechanisms preserve this exactly:

- **Case 2:** a new coordinate \(v\) born at threshold \(J\) scales every residual row \(i>J\), hence multiplies precisely \(b_{J+1},\ldots,b_M\).

- **Case 1(1):** let the chosen old divisor \(u\) have threshold \(q=J+J_1\). Before the step, \(u\) occurs in rows \(i>q\) and not in \(J<i\le q\). Scaling the latter block by \(u\) makes \(u\) occur exactly once in every row \(i>J\); its threshold changes from \(q\) to \(J\).

- **Case 1(2):** write \(u=v\,u'\). Rows \(J<i\le q\), which did not contain \(u\), acquire one \(v\) from the block scaling. Rows \(i>q\), which already contained one \(u\), acquire one \(v\) through \(u=v u'\) but receive no block scaling. Hence \(v\), again, occurs exactly once on the suffix and nowhere else.

A width drop merely truncates the chain at the new running minimum. It cannot create a non-suffix support.

There is a nearby genuine paper defect, but it does not affect this conclusion: for widths \((2,2,1,1)\), the carried profiles \((1,1,1)\) and \((2,1,0)\) become incomparable. Thus Aoyagi’s stronger total-comparability claim for the \(T\)-profiles is false. The \(b\)-chain survives because it depends only on thresholds, not cross-threshold profile comparability.

For positive widths, \(b_1\) is always nontrivial: the initial equal block forces a Case-2 blow-up at \(J=0\), producing a threshold-zero divisor. It remains in \(b_1\). It is also squarefree: the preceding case analysis shows that every exceptional coordinate occurs at most once in every \(b_i\); repeated use accumulates Jacobian exponent, not loss exponent.

If “all widths” includes zero, this fails. For example \((2,2,0)\) gives an empty/identically-zero product ideal and no meaningful nontrivial \(b_1\). That case is excluded by the stated “genuinely singular” setup.

## (2) Unit nonvanishing versus cover

**VERDICT: UNSOUND as literally stated; otherwise SOUND with a named compact-atlas bookkeeping obligation.**

If the target record requires every ideal-representation cofactor to be nonvanishing, it is already incompatible with the ordinary blow-up of \(\langle x,y\rangle\). In the chart

\[
g(u,v)=(u,uv),
\]

the pulled-back ideal is \(\langle u,uv\rangle=\langle u\rangle\), but the representation of the second generator is

\[
y\circ g=v\,u.
\]

Any continuous coefficient \(a\) satisfying \(uv=a(u,v)u\) on an open neighborhood must equal \(v\) where \(u\ne0\), hence everywhere by continuity. Therefore \(a(0,0)=0\). Nonvanishing is impossible. Ideal-identity cofactors should be continuous; only the Jacobian unit, or the determinant of a generator-change matrix, should be nonvanishing.

Under that corrected interpretation, the far-region concern is not an obstruction:

- Aoyagi’s \(Q,P\) are unipotent, so their determinants are identically \(1\).
- Terms such as \(b_i/b_{J+1}\) are monomials because of the divisibility chain; they introduce no rational pole.
- In a blow-up chart the selected projective pivot is normalized to \(1\). The exceptional coordinate itself may vanish, but it is factored into the declared Jacobian monomial and is not part of the unit.
- Choosing a maximum-modulus center coordinate gives angular ratios in \([-1,1]\), while the normalized pivot remains nonzero throughout that sector.

The nontrivial residual is the **finite compact-atlas refinement**. One must not take a single germ chart around one projective direction and enlarge it blindly. Either:

1. explicitly use max-pivot sectors at every recursive blow-up; or
2. use properness: the inverse image of a closed target ball is compact, cover it by local pivot charts, take a finite subcover, and shrink to compact domains whose closures remain inside the pivot-nonvanishing open sets.

That proves the existence of `dom ⊆ nbhd` with dom-wide certificates and a finite a.e. cover. This is standard detail-at-scale, not new resolution mathematics, but it is a genuine missing lemma if the construction only says “the pivot is nonzero near the chart origin.”

## (3) Minimum attainment and no undershoot

**VERDICT: SOUND for the physical running-min construction; Aoyagi’s printed raw-width labelling is UNSOUND.**

Let

\[
r_s=\min(M^{(1)},\ldots,M^{(s)}).
\]

A Case-2 divisor born at stage \(S\), threshold \(J\), has the corrected physical profile

\[
t_i=r_{i+1}\quad(i<S),\qquad t_i=J\quad(i\ge S).
\]

It is weakly decreasing and satisfies the running-min bounds. Its envelope-prefix contributions to \(M_{\mathrm{val}}\) vanish because

\[
(M^{(1)}-r_2)(M^{(2)}-r_2)=0
\]

and

\[
(r_j-r_{j+1})(M^{(j+1)}-r_{j+1})=0.
\]

Consequently,

\[
M_{\mathrm{val}}(t)=(r_S-J)(M^{(S+1)}-J),
\]

exactly the Case-2 Jacobian exponent.

For Case 1, lowering a constant tail from \(q=J+J_1\) to \(J\) changes \(M_{\mathrm{val}}\) by

\[
(q-J)(M^{(S+1)}-J)
   =J_1(M^{(S+1)}-J),
\]

exactly Aoyagi’s accumulated-exponent update. Induction therefore proves that every physical terminal exponent is \(M_{\mathrm{val}}(t)\) for an admissible terminal profile \(t\). Hence every such exponent is at least `qipMin`.

For \((2,2,3,2)\), the printed label \((2,3,0)\) gives

\[
M_{\mathrm{val}}(2,3,0)=6,
\]

whereas the physical exponent is \(4\). Running-min correction gives \((2,2,0)\), and

\[
M_{\mathrm{val}}(2,2,0)=4.
\]

Meanwhile `qipMin = 3`, attained by \((1,1,0)\), so the disputed exponent is nonbinding and does not undershoot.

Attainment requires a separate argument; it does not follow merely from the lower bound. Not every admissible profile is realized. For example, at \((3,3,4,2,3)\), the admissible profiles \((2,2,2,0)\) and \((3,2,2,0)\) are stranded and never become terminal.

Nevertheless every minimizer is realized. If an admissible profile has a forbidden descent from a saturated running minimum, replace its preceding prefix by the running-min envelope. The envelope contributes zero; the original non-envelope prefix contributes strictly positively; the boundary and suffix terms are unchanged. Thus the replacement strictly decreases \(M_{\mathrm{val}}\), so a non-clearable profile cannot minimize. A clearable minimizer is then realized by steering the Case-1 recursion through its successive descents. This supplies the required attaining axis.

That exponent ledger and steering induction are detail-at-scale. They are not a new-mathematics frontier.

The single most likely thing to be wrong is the requirement that ideal-identity cofactors be nonvanishing. The elementary chart \(g(u,v)=(u,uv)\) disproves it exactly. If only continuity was intended, the likeliest remaining gap is the finite compact-atlas refinement, not the divisor algebra.