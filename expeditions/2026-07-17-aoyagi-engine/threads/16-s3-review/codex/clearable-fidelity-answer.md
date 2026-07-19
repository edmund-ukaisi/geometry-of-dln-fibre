**Q1 — PROVED.** The predicates are equivalent for every \(a\in\mathrm{Adm}\).

For any strict descent at \(S\),

\[
a^{S-1}>a^S\ge 0,
\]

so \(S\le \operatorname{clear}(a)\). Admissibility at coordinate \(S-1\) gives

\[
a^{S-1}\le e_{S-1}=r_S.
\]

Moreover,

\[
b(a)<S
\iff
\text{the prefix }1,\ldots,S-1\text{ is not entirely equal to the envelope}.
\]

Thus, at every strict descent, the two predicates say respectively

\[
b<S\Longrightarrow a^{S-1}<r_S
\]

and

\[
a^{S-1}=r_S\Longrightarrow b\ge S.
\]

Because \(a^{S-1}\le r_S\), these are contrapositives. Hence both directions hold.

Boundary checks:

- If \(b=1\), every nonempty prefix already fails to equal the envelope; both predicates therefore forbid every saturated strict descent.
- If \(b=\operatorname{clear}\), the primary range is empty. Every strict descent has \(S\le\operatorname{clear}=b\), hence its prefix is still envelope-equal, so saturation also holds.
- A later return to the envelope is eventually rejected. For example,

  \[
  M=(5,5,3,2,2),\qquad a=(5,2,2,0)
  \]

  has \(e=(5,3,2,2)\), \(b=2\), and touches the envelope again at coordinate \(3\). The descent at \(S=4\) starts from \(a^3=r_4=2\), so both predicates fail.
- Ties trigger neither predicate.
- Literally \(a=e\) at every coordinate is impossible here, since \(a^L=0<e_L\). The meaningful “all-envelope” boundary is equality through the positive support, giving \(b=\operatorname{clear}\).

**Q2 — COUNTEREXAMPLE-at-\(M=(3,3,3),\,a=(2,0)\)** to redundancy.

Here \(L=2\), \(r_2=3\), and \(a\in\mathrm{Adm}\). At \(S=2\),

\[
a^2=0<a^1=2<r_2=3.
\]

Thus strict descent does not imply saturation. The saturation antecedent is false at this \(S\), so its implication is vacuously true. Both predicates accept this profile.

**Q3 — UNSURE.**

Inference: the predicates exactly encode the stated post-birth stranding obstruction. A saturated post-birth descent is unreachable at layer \(S\), and later thresholds cannot improve because \(r_S\) is non-increasing.

But that obstruction alone does not prove sufficiency: one still needs that every level below \(r_S\) is constructively reachable and that multiple clearing choices are mutually compatible.

There is also a concrete ambiguity:

\[
M=(3,3,3),\qquad a=(3,0).
\]

Here \(b=\operatorname{clear}=2\), and both predicates accept \(a\), despite the birth descent starting at \(a^1=r_2=3\), above the layer-\(2\) reachable ceiling \(2\). If this birth descent represents a divisor requiring clearing, this is a false positive. If birth is an initialization step exempt from clearing, it is harmless. The stated stranding mechanism does not determine which interpretation is correct.