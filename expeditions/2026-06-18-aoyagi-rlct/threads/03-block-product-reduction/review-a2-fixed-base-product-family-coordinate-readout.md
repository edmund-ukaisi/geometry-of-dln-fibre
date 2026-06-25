# Review - A2 fixed-base product-family coordinate readout

Date: 2026-06-25.

## Verdict

Passed at the finite coordinate-readout scope.

## Checks

The proof route is a specialization and readout:

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges
  -> suffixState_productFamily_fields_fromBlocks_succSucc
  -> paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields
```

The sign convention is consistent with the p.13 cleaned coordinates:

```text
S.B = -F2     so -S.B = F2,
S.L = [I,0;F3,I] so lowerLeftBlock S.L = F3.
```

The residual coordinate remains

```text
residualProduct EMat last 0
```

which records the edgewise residual-factor caveat from the source audit.

## Residual Risk

The transformed-edge hypotheses are still assumptions.  A later product-family
constructor must build the fixed-base continuous edge family and prove these
block shapes before the socket can feed the lower-bound and local-measure
front ends.
