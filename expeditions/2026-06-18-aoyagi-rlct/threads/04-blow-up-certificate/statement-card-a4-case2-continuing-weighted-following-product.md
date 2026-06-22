# Statement card - A4 Case 2 continuing weighted following product

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withCorrectedPostData`

## Statement

For Aoyagi's displayed Case 2 source chart, right-multiply the continuing
weighted lower-row paper-`C'` handoff by an arbitrary supplied following
product `F`.  The theorem states that the lower rows of the source-side
weighted `Q/P` product, after multiplication by `F`, equal

```text
(diagonal(successor lower-row weights)
  *
  (case2DisplayedPostPivotResidualBlock
    * case2SourceFollowingFactor at (S,J+1))) * F.
```

The theorem also carries the corrected post-data projections already supplied
by the source-chart boundary.

## Proved

Lean proves only equality preservation under right multiplication by a
supplied `F`, using the existing paper-`C'` weighted lower-row handoff.  The
proved theorem keeps the same witness `q` and carries the corrected post-data
projections from the existing source-chart boundary.

## Assumed

- Displayed Case 2 source-chart hypotheses.
- Pre exponent certificates, level invariants, least-value gap, and chart
  family boundary.
- A source-coordinate following factor `C : Nat -> tau -> R`.
- A supplied following product `F : Matrix tau upsilon R`.

## Cited

- None in Lean.  This is finite matrix algebra and equality congruence.

## Deferred

- Source production of `F`.
- Full source production of `C'^(S+1)`.
- Pivot-row inclusion.
- Next-center nonemptiness.
- Terminal relabeling, actual-width or row-exhausted terminal branches.
- Chart coverage, successor chart-family construction, chart-produced
  recurrence/exponent post-data, transition invariance, Jacobian arithmetic,
  normal crossings, pole order, and RLCT extraction.

## Review

- xhigh Lean API scout `Carver` recommended this as the smallest useful Lean
  theorem after the paper-`C'` frontier audit.
- xhigh source scout `Halley` identified the broader successor-following
  object as a future target; this card deliberately takes only the
  right-multiplication lower-row slice.
- xhigh reviewer `Cicero` passed the landed theorem and checked that it keeps
  the lower-row-only, supplied-`F`, explicit-diagonal, and corrected-post-data
  boundaries.

## Verification

- `cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `cd lean && lake build DLNFibre` passed, with only pre-existing Core
  warnings.
- `cd lean && scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
