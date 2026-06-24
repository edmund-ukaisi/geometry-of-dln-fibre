# Statement card - A2 product-reduction triangular coordinate chart

## Lean Names

- `DLNFibre.DLN.Aoyagi.ProductReductionStepRawCoordinates`
- `DLNFibre.DLN.Aoyagi.ProductReductionStepChartCoordinates`
- `DLNFibre.DLN.Aoyagi.ProductReductionStepRawCoordinates.detChart`
- `DLNFibre.DLN.Aoyagi.ProductReductionStepChartCoordinates.detChart`
- `DLNFibre.DLN.Aoyagi.ProductReductionStepRawCoordinates.toChart`
- `DLNFibre.DLN.Aoyagi.ProductReductionStepChartCoordinates.toRaw`
- `DLNFibre.DLN.Aoyagi.ProductReductionStepRawCoordinates.detChart_toChart`
- `DLNFibre.DLN.Aoyagi.ProductReductionStepChartCoordinates.detChart_toRaw`
- `DLNFibre.DLN.Aoyagi.productReductionStepCoordinate_left_inverse`
- `DLNFibre.DLN.Aoyagi.productReductionStepCoordinate_right_inverse`

## Claim

The one-step p. 13 product-reduction variables form an explicit triangular
coordinate change on determinant charts.  The raw variables are

```text
C1, D, F3, A1, A2, A3, A4,
```

and the chart variables are

```text
Ctop, D, A1, A3, F2, F3, C.
```

The passive variables `D`, `A1`, and `A3` are retained, and no inverse of `D`
is used.

## Proved

The forward map is

```text
Ctop = C1*A1,
F2   = -(A1^(-1)*A2),
F3   = F3old - D*A3*(C1*A1)^(-1),
C    = A4 - A3*A1^(-1)*A2.
```

The inverse map is

```text
C1    = Ctop*A1^(-1),
A2    = -A1*F2,
A4    = C - A3*F2,
F3old = F3 + D*A3*Ctop^(-1).
```

Lean proves forward-then-inverse on the raw determinant chart and
inverse-then-forward on the target determinant chart.  It also proves that
the determinant-chart domains are preserved by both maps.

## Deferred

The next structure-level wrappers should connect these coordinates to the
existing block identities:

- `productReduction_chartLocalInductionStep_fromBlocks_indexed`;
- `triangularBlockProductDifference_fromBlocks_indexed`;
- the entry-ideal cleanup in `ProductReductionEntryIdealBoundary.lean`.

## Nonclaims

This is not exact-rank openness, analytic coordinate chart construction,
chart coverage, analytic germ transport, Jacobian/prior compatibility,
regular-coordinate RLCT additivity, normal crossings, pole order, or RLCT
extraction.

## Review

Focused Lean check passed for `DLNFibre.DLN.Aoyagi.ProductReduction`.
Independent xhigh reviewer `Turing the 4th` passed the slice after repairs:
the left inverse is now stated on the raw determinant chart, the source
wording distinguishes Aoyagi's literal `C1' A1'` chart from the equivalent
Lean determinant-domain presentation, and block-difference wrappers are marked
deferred.
