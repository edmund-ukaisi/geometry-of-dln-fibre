# Statement card - A2 formal-product/source-image theta-side density constructor

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaFormalProductSourceImageContract.lean
```

Names:

```text
A2Case2FormalProductSourceImagePieceContract.formalProduct_restrict_eq_withDensity_of_restrict_eq_map_sourceChart_withDensity
A2Case2FormalProductSourceImagePieceContract.exists_of_restrict_eq_map_sourceChart_withDensity
```

## Claim

If a formal-product chart measure restricted to `chartPiece` is already known
to be the source-chart pushforward of the theta reference measure weighted by

```text
theta => density (sourceChart theta),
```

then it is the chart-produced source-image reference with edge-side density
`density`, restricted to the same chart piece.

Equivalently, this theorem lets later raw/source-chart work feed the
bounded-density contract using a theta-side weighted pushforward identity.

## Inputs

- measurable `V`;
- a.e.-measurable `sourceChart` for `thetaReference.restrict V`;
- a.e.-measurable `density` for
  `Measure.map sourceChart (thetaReference.restrict V)`;
- the theta-side weighted pushforward equality;
- for the constructor form, the existing local source-chart fields:
  measurable `chartPiece`, measurable image, image containment,
  continuity on `V`, injectivity on `V`, and left inverse on `V`;
- the a.e. bound `density <= bound` on the restricted source image reference.

## Output

The equality conversion produces:

```text
formalProductMeasure.restrict chartPiece =
  (((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
    .restrict chartPiece)
```

The constructor form produces an
`A2Case2FormalProductSourceImagePieceContract` with the supplied
`sourceChart`, `readback`, `thetaReference`, `V`, `chartPiece`,
`formalProductMeasure`, `density`, and `bound`.

## Dependencies

- `measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq` from
  `lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`;
- the existing `A2Case2FormalProductSourceImagePieceContract` fields.

## Nonclaims

No Jacobian density is computed.  No density bound is proved.  No
formal-product/source-image domination follows unless the caller also supplies
the theta-side equality and bound.  No raw-Haar transport, determinant-chart
Haar equality, source-image coverage, original prior transport, normal
crossings, pole order, or RLCT extraction is proved.
