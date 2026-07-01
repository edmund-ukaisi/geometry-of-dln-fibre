# Statement Card - A2 Source-image Chart-piece Density Readback Domination to W

## Claim

A bounded-density identity on a measurable source-side chart piece supplies
both readback a.e.-measurability and readback domination by the coordinate
reference measure restricted to any larger coordinate set `W` containing the
local chart domain `V`.

Public Lean names:

```text
aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity

aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn

originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_coordinateSourceMeasure_restrict_of_sourceImageReference_eq_withDensity_of_continuousOn_injOn
```

## Inputs Used

- `MeasurableSet V`, `MeasurableSet chartPiece`, and `V subset W`;
- local source-chart a.e. measurability/readback a.e. measurability, or the
  continuous injective local chart data that generate them;
- local left inverse `readback (sourceChart theta) = theta` on `V`;
- restricted bounded-density identity on `chartPiece`;
- a.e. upper bound for that density over the chart-piece source reference.

## Output

```text
AEMeasurable readback (externalMeasure.restrict chartPiece)
Measure.map readback (externalMeasure.restrict chartPiece) <=
  c • thetaReference.restrict W
```

The p.13 specialization uses `externalMeasure = originalEdgeFamilyVolume` for
the fixed p.13 endpoint bases.

## Nonclaims

No original/source density identity is proved.  No source-image coverage,
source-rank coverage, Haar transport, Jacobian formula, normal crossings, pole
order, or RLCT extraction is proved.
