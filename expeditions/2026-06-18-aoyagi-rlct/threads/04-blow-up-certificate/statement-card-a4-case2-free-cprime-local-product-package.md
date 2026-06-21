# Statement card - A4 Case 2 free Cprime local product package

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Expected names:

- `DLNFibre.DLN.Aoyagi.sourceChartMap_constructedSourceFreeCprimeLocalProduct_withCorrectedPostData`

## Statement

For the displayed Case 2 pivot chart, a free pivot-first chart-coordinate
following matrix `Cprime` can be used in two paired finite identities:

- reconstruct the old source residual following factor as `Q*Cprime`, giving
  the source-displayed `Q/P` product identity with `D''' * Cprime`;
- project the lower rows of `D''' * Cprime` to the continuing `(S,J+1)` block
  product with the reindexed free tail of `Cprime`.

A concrete source-chart package may conjoin these product identities with the
existing corrected post-data projections.

## Proved

- The old source residual following factor reconstructed from `Q*Cprime`
  satisfies the source-displayed weighted `Q/P` product identity.
- The bare lower rows of `D''' * Cprime` reindex to the post-pivot residual
  block times the reindexed free tail.
- The concrete source-chart theorem pairs these identities with existing
  corrected exponent, level, least-value-gap, and `case2Gap` projections.

## Assumed

- Displayed Case 2 supplied boundary data.
- For the concrete package, the existing pre-state exponent, level,
  least-value-gap, and chart-family boundary hypotheses.

## Cited

- None in Lean.  This is finite matrix algebra and reindexing.

## Deferred

- Chart coverage, arbitrary-pivot coverage, source production of `Cprime`,
  successor matrix construction, chart-produced recurrence/exponent data,
  transition invariance, terminal relabeling, Jacobian arithmetic, normal
  crossings, pole order, and RLCT extraction.

## Review

- xhigh source checker `Aristotle` accepted the package as source-faithful
  for the displayed top-left Case 2 chart, with the precision condition that
  the weighted `Q/P` equality and the bare lower-row `D''' * Cprime` equality
  remain distinct.
- xhigh Lean API scout `Ramanujan` recommended the single concrete package
  theorem above and typechecked its shape via `lake env lean --stdin`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
