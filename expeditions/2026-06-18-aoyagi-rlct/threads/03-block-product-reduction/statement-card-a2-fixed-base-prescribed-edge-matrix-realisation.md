# Statement Card - A2 fixed-base prescribed edge-matrix realisation

Date: 2026-06-25.

## Claim

Prescribed fixed-base edge matrices can now be realised by actual reversed
edge maps, and by continuous reversed edge maps in the finite-dimensional
topological setting.  Reading those realised maps back in the same fixed
endpoint bases returns the prescribed matrices exactly.

For chains with at least two edges, if the prescribed matrices satisfy the
product-family transformed-edge block-shape hypotheses, then the fixed-base
continuous edge family built from them has cleaned p.13 product-difference
coordinates

```text
value(Ctop - I, F2, F3, residualProduct G last 0).
```

## Lean Artifacts

```text
paperEndpointFixedBaseReverseEdgeFamilyOfMatrices
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_reverseEdgeFamilyOfMatrices
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_prescribedProductFamilyEdgeMatrices_succSucc
```

## Inputs Kept Explicit

- the prescribed edge matrices `G`;
- the product-family transformed-edge block-shape hypotheses on `G`;
- `IsUnit Ctop.det`;
- finite-dimensional hypotheses needed to turn linear maps into continuous
  linear maps.

## Nonclaims

No product-coordinate matrix family `G(x,u)` is constructed.  No transformed
edge shape is proved from a concrete `G(x,u)`.  No parameter-continuity,
product chart, source coverage, signed-box pushforward, density/Jacobian
transport, normal crossings, pole order, or RLCT extraction is proved.

## Verification

Checked with:

```text
cd lean
LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.FixedBasepointChart
LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```
