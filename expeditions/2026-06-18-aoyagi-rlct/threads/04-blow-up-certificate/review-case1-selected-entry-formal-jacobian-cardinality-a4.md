# Review - A4 Case 1 selected-entry formal Jacobian cardinality

Status: reviewed; no blockers found.

## Reviewers

- Source and pen-and-paper scout: xhigh `Sartre`.
- Lean/API scout: xhigh `Boyle`.

## Source And Math Review

The source scout checked Aoyagi PDF pp. 15-18/19.  The source anchors are:

- PDF p. 15: the inductive volume-form display contains the row-strip factor
  over `J+1 <= i <= M^(S)` and `J+1 <= j <= M^(S+1)`, together with old
  exceptional factors.
- PDF p. 16: Case 1 prints the blow-up center
  `d_ij = 0` for `J+1 <= i <= J+J1`, `J+1 <= j <= M^(S+1)`, and
  `u_(s,k)=0`.
- PDF p. 16, Case 1(1): the old-exceptional chart divides the row strip by
  `u_(s,k)` and prints the increment
  `M'_(s,k)=M_(s,k)+J1*(M^(S+1)-J)`.
- PDF pp. 16-17, Case 1(2): the top-left row-strip chart sets
  `u_(s,k)=u_(S,J+1)u'_(s,k)` and prints the same increment for the new pivot
  variable.

The pen-and-paper count is:

```text
r = J1 * (M^(S+1)-J)
```

row-strip entries and `1+r` total center generators.  Erasing either displayed
pivot leaves `r` non-pivot generators.  Hence the formal selected-entry
determinant exponent is `r` in both displayed Case 1 charts.

## Lean/API Review

The Lean/API scout confirmed that this slice was not already fully
formalised.  The generic selected-entry determinant and the Case 2
specialization existed, while Case 1 had center membership and
principalization scaffolding whose statement cards still explicitly deferred
Jacobian formulas.

The recommended implementation path was:

- prove the row, column, row-strip, and center cardinality lemmas;
- prove a generic erased-pivot cardinality lemma for any Case 1 center member;
- specialize it to the old generator and displayed row-strip pivot;
- specialize `selectedEntryPivotFirstJacobian_det` to both displayed Case 1
  finite selected charts.

The implementation follows this path.

## Boundary Check

No analytic conclusion is claimed.  The new Lean facts are finite selected
chart algebra only.  They do not construct charts, prove coverage, prove
source-produced recurrence or exponent post-data, identify an analytic
Jacobian/volume form, prove transition regularity, normal crossings, pole
order, or RLCT extraction.

Independent xhigh follow-up reviewer `Sagan` passed the final diff with no
findings.  The reviewer confirmed that the Lean additions are finite
cardinality/formal-determinant facts and that the docs keep the analytic and
RLCT boundary explicit.

## Verification

Controller ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```

The focused build, full build, no-sorry audit, and diff hygiene check passed
through the shared-store `scripts/lb` workflow.  The full build emitted only
pre-existing Core warnings.
