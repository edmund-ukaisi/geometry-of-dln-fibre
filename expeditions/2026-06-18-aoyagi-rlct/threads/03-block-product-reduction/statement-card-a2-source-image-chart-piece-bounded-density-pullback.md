# Statement Card - A2 Source-image Chart-piece Bounded-density Pullback

## Claim

For a local source chart with readback, if an external source-side measure
restricted to a measurable chart piece is identified as a bounded-density
perturbation of the chart-produced source-image reference, then its readback
pullback is dominated by the coordinate reference measure on `V`.

Public Lean names:

```text
measure_map_readback_restrict_piece_le_smul_of_restrict_eq_withDensity

measure_map_readback_restrict_piece_le_smul_of_restrict_eq_withDensity_of_continuousOn_injOn
```

## Inputs Used

- `MeasurableSet V` and `MeasurableSet chartPiece`;
- `AEMeasurable sourceChart (thetaReference.restrict V)`;
- `AEMeasurable readback (Measure.map sourceChart (thetaReference.restrict V))`;
- `readback (sourceChart theta) = theta` on `V`;
- equality of the restricted external measure with a restricted `withDensity`
  perturbation of `Measure.map sourceChart (thetaReference.restrict V)`;
- a.e. upper bound `density <= c` over that chart-piece restriction.

The `_of_continuousOn_injOn` variant replaces the two a.e.-measurability inputs
with `ContinuousOn sourceChart V`, `Set.InjOn sourceChart V`, and the local
left inverse.

## Output

```text
Measure.map readback (externalMeasure.restrict chartPiece)
  <= c • thetaReference.restrict V
```

## Nonclaims

No original DLN prior is constructed.  No source-image coverage, source-rank
coverage, Haar transport, Jacobian formula, normal crossings, pole order, or
RLCT extraction is proved.
