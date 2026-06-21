# Review - A4 Case 2 free Cprime local product package

Status: reviewed and formalised.

## Scope Check

The target is a paired product package, not a transition theorem.  It should
reuse the existing constructed-source `Q/P` theorem and the free-`Cprime`
post-pivot lower-row theorem, adding no new algebra beyond conjunction and
concrete source-chart post-data packaging.

## Risks

- The theorem name must not suggest chart coverage or source production.
- The old following factor is reconstructed as a source-coordinate
  representative; this is finite bookkeeping, not an analytic atlas statement.
- Corrected exponent/level fields remain supplied/corrected post-data.
- The `Q/P` identity has a successor row-weight diagonal on the right.  A
  package that also mentions the post-pivot lower-row product must either keep
  the bare `D''' * Cprime` lower-row equality separate or explicitly prove the
  weighted lower-row projection.

## Verdict

Proceed with the single concrete source-chart package recommended by the Lean
API scout.  Keep the weighted `Q/P` equality and the bare lower-row equality as
separate conjuncts.

## Xhigh Checks

Source checker `Aristotle` accepted the package for Aoyagi pp. 19-22 under the
displayed top-left pivot scope.  The only required precision fix was to avoid
saying the lower-row theorem applies to the weighted right side of the `Q/P`
identity; the lower-row theorem is for bare `D''' * Cprime`.

Lean API scout `Ramanujan` recommended one concrete theorem combining
`sourceDisplayedQP_constructedSourceFollowingFactor_paperQP` with
`sourceChartMap_postPivotFreeCprimeNextSameStageProduct_withCorrectedPostData`,
and advised not adding a next-continuation/nonempty frontier field in this
slice.
