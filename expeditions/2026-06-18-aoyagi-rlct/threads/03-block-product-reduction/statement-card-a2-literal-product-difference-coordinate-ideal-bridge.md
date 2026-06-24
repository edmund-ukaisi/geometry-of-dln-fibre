# Statement card - A2 literal product-difference coordinate ideal bridge

## Lean Name

- `DLNFibre.DLN.Aoyagi.AoyagiProductDifferenceCoordinateIndex.matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal`

## Claim

The literal signed/corrected p. 13 product-difference block generates the same
ideal as the combined product-difference scalar coordinate family:

```text
matrixEntryIdeal (fromBlocks X (-F2) (-F3) (D - F3*F2))
  =
AoyagiProductDifferenceCoordinateIndex.entryIdeal X F2 F3 D.
```

## Proved

Lean proves the claim over an arbitrary commutative ring.  The theorem assumes
`Fintype iota`, the finite summation index required for the product `F3*F2`.
No determinant, inverse, topology, or analytic hypothesis is used.

The proof composes:

- the existing signed-block cleanup
  `matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_fourMatrixEntryIdeal`;
- the existing coordinate-index ideal identity
  `AoyagiProductDifferenceCoordinateIndex.entryIdeal_eq_fourMatrixEntryIdeal`.

## Nonclaims

No analytic coordinate chart, regular-suspension chart construction, analytic
germ-ideal transport, chart coverage, Jacobian compatibility, normal
crossings, pole order, or RLCT extraction is proved.
