# Statement card - A2 suffix-state step coordinate adapter

## Lean Names

- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.stepRawCoordinates`
- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.stepRawCoordinates_detChart`
- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.stepRawCoordinates_toChart_Ctop`
- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.stepRawCoordinates_toChart_F2`
- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.stepRawCoordinates_toChart_C`
- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.stepRawCoordinates_toChart_D_mul_C`
- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.stepRawCoordinates_toChart_F3_of_L_eq_lowerUnitriangular`
- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.stepRawCoordinates_priorProduct`
- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.stepRawCoordinates_triangularBlockProduct`
- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.stepRawCoordinates_productDifference`

## Claim

One deterministic suffix-state step supplies the prior product hypothesis
needed by the p. 13 coordinate wrapper.  Given `S.BlockDiagonal P hpj`, a
lower-unitriangular presentation

```text
S.L = [I 0; F3prev I],
```

and the transformed-edge determinant chart, the raw coordinates built from
`S.Ctop`, `S.D`, `F3prev`, and the four corners of
`transformedEdge E p S` give the p. 13 triangular product and signed
product-difference identities for

```text
T = P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj).
```

## Proved

Lean proves:

- determinant-chart membership for the raw step coordinates;
- field bridges from `x.toChart` to `step E p S`;
- the prior product identity supplied by `S.BlockDiagonal`;
- the triangular block-product identity;
- the signed product-difference identity with lower-right correction `F3*F2`.

The determinant chart is imposed on `transformedEdge E p S`, not on raw `E p`.
No inverse of `S.D` is used.

## Deferred

The actual recursive `suffixState` specialization is recorded separately in
`statement-card-a2-suffix-state-step-coordinate-specialization.md`.  The
coordinate-ideal naming bridge remains in the ideal/coordinate layer.

## Nonclaims

No exact-rank openness, analytic coordinate-chart construction, chart
coverage, analytic germ transport, ideal transport, normal crossings, pole
order, or RLCT extraction is proved.
