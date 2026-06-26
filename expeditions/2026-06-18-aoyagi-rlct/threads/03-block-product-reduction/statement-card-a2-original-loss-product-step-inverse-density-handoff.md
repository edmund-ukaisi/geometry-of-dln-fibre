# Statement Card - A2 original-loss product-step inverse-density handoff

Date: 2026-06-26.

## Claim

The original-loss p.13 product-family finite-integral front end can be stated
with the concrete chart-side inverse product-step Jacobian density along
`paperEndpointFixedBaseP13RawOrderTuple`, rather than an abstract positive
continuous density factor.

## Lean Name

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase
```

## Proved

The theorem specializes the existing original-loss edge-matrix product-family
handoff by setting

```text
density xu =
  productReductionStepRawOrderInverseJacobianDensity
    (paperEndpointFixedBaseP13RawOrderTuple V Bv U0 hU0 CedgeBase xu).
```

The already-proved p.13 inverse-density lemmas supply `ContinuousAt density
(x0,0)` and `0 < density (x0,0)`.

## Assumed

The signed-box source chart, weighted source pushforward, residual monomial
lower bound, source-density monomial upper bound, fixed-base edge-matrix
measurability, and exponent inequality remain explicit hypotheses inherited
from the existing front end.

## Cited

None.  This is finite-integral plumbing using already-proved local continuity
and positivity facts.

## Deferred

No product chart construction, source coverage theorem, product-step/source
pushforward, signed-box density identification, original prior transport,
normal-crossing production, pole-order theorem, or RLCT theorem is proved.

## Verification

Focused module build passed:

```text
cd lean && env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure
```

Review passed:
`review-a2-original-loss-product-step-inverse-density-handoff.md`.
