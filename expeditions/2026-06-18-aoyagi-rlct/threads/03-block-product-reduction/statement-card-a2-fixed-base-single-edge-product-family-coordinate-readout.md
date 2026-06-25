# Statement Card - A2 fixed-base single-edge product-family coordinate readout

Date: 2026-06-25.

## Claim

The fixed-base p.13 coordinate readout now covers the single-edge
product-family case.  If the transformed fixed-base edge matrix is

```text
[ Ctop,        -Ctop F2
  -F3 Ctop,    C0 + F3 Ctop F2 ],
```

with `IsUnit Ctop.det`, then the cleaned fixed-base product-difference
coordinate map is

```text
value(Ctop - I, F2, F3, C0).
```

The same conclusion holds for the continuous fixed-base edge map realised from
a prescribed one-edge matrix `G`.

## Lean Artifacts

```text
paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdge_one
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdge_one
paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_prescribedProductFamilyEdgeMatrix_one
```

## Nonclaims

No product-coordinate family is constructed.  No transformed-edge shape is
proved for a concrete product family.  No parameter-continuity, product chart,
source coverage, density/Jacobian transport, normal crossings, pole order, or
RLCT extraction is proved.

## Verification

Checked with:

```text
cd lean
LAKE_SHARED=$PWD/.lake-local-shared scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```
