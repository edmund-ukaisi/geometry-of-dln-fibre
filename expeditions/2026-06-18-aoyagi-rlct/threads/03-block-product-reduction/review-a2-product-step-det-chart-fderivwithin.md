# Review - A2 product-step determinant-chart `fderivWithin`

Date: 2026-06-26.

Verdict: accepted at the stated narrow scope.

## Checks

- The open set is exactly the ambient raw determinant chart
  `{z | IsUnit z.1.det and IsUnit z.2.2.2.1.det}`. This matches
  `ProductReductionStepRawCoordinates.detChart` after replacing record fields
  by tuple projections.
- The openness proof uses only continuous tuple projections, determinant
  continuity, and the open unit locus. No source-rank or analytic chart
  coverage assumption is hidden.
- The `HasFDerivWithinAt` theorem is a direct restriction of the landed
  ambient `HasFDerivAt` theorem. This is the correct vector-space API for the
  open-domain derivative.
- The `fderivWithin` determinant theorem rewrites by `fderivWithin_of_isOpen`
  and reuses the landed ambient `fderiv` determinant-unit theorem. No new
  determinant calculation is introduced.

## Boundary

The theorem deliberately avoids a derivative statement on the subtype
`{z // z in S}`. That subtype is a topological space, not the vector space
domain expected by plain Frechet derivative APIs. A later manifold or local
homeomorphism package may use this open-domain theorem, but it should be a
separate statement.

This checkpoint still does not prove injectivity/local inverse hypotheses for
Mathlib's measure change-of-variables theorem, source-measure pushforward,
density transport, normal crossings, pole order, or RLCT.
