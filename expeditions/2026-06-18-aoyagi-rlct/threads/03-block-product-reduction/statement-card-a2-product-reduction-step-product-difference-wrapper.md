# Statement card - A2 product-reduction step product-difference wrapper

## Lean Names

- `DLNFibre.DLN.Aoyagi.productReductionStepCoordinate_triangularBlockProduct`
- `DLNFibre.DLN.Aoyagi.productReductionStepCoordinate_productDifference`

## Claim

The p. 13 one-step coordinate package feeds the existing block-product and
product-difference identities.  Given raw coordinates `x` on the determinant
chart and a prior triangular product hypothesis

```text
[I 0; x.F3 I] T =
  [x.C1 0; 0 x.D] [x.A1 x.A2; x.A3 x.A4],
```

the chart coordinates `y = x.toChart` satisfy

```text
[I 0; y.F3 I] T [I y.F2; 0 I] =
  [y.Ctop 0; 0 y.D y.C].
```

After subtracting the rank-model block `[I 0; 0 0]`, the signed
product-difference block is

```text
[y.Ctop - I, -y.F2; -y.F3, y.D y.C - y.F3 y.F2].
```

## Proved

Lean proves both equalities over an arbitrary commutative ring and finite index
types, with determinant-chart hypothesis `x.detChart`.  The proof uses:

- `lowerUnitriangular_mul_fromBlocks_one_zero_indexed`;
- `productReduction_chartLocalInductionStep_fromBlocks_indexed`;
- `triangularBlockProductDifference_fromBlocks_indexed`.

No inverse of `D` is introduced.  The lower-right correction is `F3*F2`.

## Deferred

The suffix-state adapter that instantiates the prior product hypothesis from
`ChartLocalSuffixState.BlockDiagonal` remains a later wrapper.  The coordinate
ideal bridge to `AoyagiProductDifferenceCoordinateIndex.entryIdeal` is also a
separate ideal-layer naming slice.

## Nonclaims

This is not exact-rank openness, analytic coordinate-chart construction,
chart coverage, analytic germ transport, Jacobian/prior compatibility,
regular-coordinate RLCT additivity, normal crossings, pole order, or RLCT
extraction.
