# Statement card - A2 suffix-state step coordinate specialization

## Lean Names

- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_stepRawCoordinates_triangularBlockProduct`
- `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_stepRawCoordinates_productDifference`

## Claim

For the actual recursive suffix state

```text
S = suffixState E j p.succ hpj,
```

the p. 13 raw-step coordinates can be chosen so that the generic
suffix-state adapter gives both the next triangular product and the signed
product-difference block for

```text
T = P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj).
```

The raw `A1`, `A2`, `A3`, and `A4` blocks come from
`transformedEdge E p S`, while `T` is the suffix product being changed by the
triangular multipliers.

## Proved

Lean proves, under `S.BlockDiagonal P hpj` and the determinant chart for
`transformedEdge E p S`, that there exists

```text
F3prev : Matrix (kappa j) rho K
```

such that `x = stepRawCoordinates E p S F3prev` and `y = x.toChart` satisfy

```text
[I 0; y.F3 I] T [I y.F2; 0 I] = [y.Ctop 0; 0 y.D*y.C]
```

and

```text
[I 0; y.F3 I] (T - [I 0; 0 0]) [I y.F2; 0 I]
  = [y.Ctop - I, -y.F2; -y.F3, y.D*y.C - y.F3*y.F2].
```

The witness `F3prev` is obtained from
`suffixState_L_eq_lowerUnitriangular`.

## Deferred

This card does not derive `S.BlockDiagonal P hpj` from the full recursive
chart hypotheses.  That remains the role of `suffixState_blockDiagonal` and
outer callers.

The coordinate-ideal naming bridge remains in the ideal/coordinate layer.

## Nonclaims

No analytic coordinate chart, chart coverage, exact-rank/source-rank openness,
regular-suspension construction, ideal transport, normal crossings, pole
order, or RLCT extraction is proved.  No inverse of `S.D` or `y.D` is used.
