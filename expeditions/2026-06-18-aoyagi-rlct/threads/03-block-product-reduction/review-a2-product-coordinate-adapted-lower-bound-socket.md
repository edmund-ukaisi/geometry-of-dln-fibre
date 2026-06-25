# Review - A2 product-coordinate adapted lower-bound socket

Date: 2026-06-25.

Reviewer: xhigh Faraday the 5th.

## Scope

Reviewed the theorem

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_nhdsWithin_source
```

in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`, together
with the reproduction and statement card for this slice.

## Findings

The reviewer found no wrong inequality direction and no accidental claim of
product-chart construction, source coverage, signed-box transport, normal
crossings, pole order, or RLCT extraction.

Two low-severity fidelity issues were identified:

- The first version did not assume `0 < Rmax`, so when `Rmax <= 0` the ball
  guard made the conclusion vacuous.  This was fixed in Lean by adding
  `hRmax : 0 < Rmax`.
- The first reproduction/card phrasing suggested that the Lean theorem exposed
  `F2/F3` smallness.  The theorem actually assumes the cleaned-to-literal
  comparison directly.  The notes were corrected; deriving that comparison
  from `F2/F3` smallness for a concrete product family remains a separate
  constructor obligation.

## Verdict

Passed after the two clarifications above.

Verified with:

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
```
