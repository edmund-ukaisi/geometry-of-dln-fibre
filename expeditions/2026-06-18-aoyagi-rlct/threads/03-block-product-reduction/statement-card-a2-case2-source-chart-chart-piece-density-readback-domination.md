# Statement Card - A2 Case 2 source-chart chart-piece density readback domination

## Claim

On the local passive-theta endpoint source-chart image, a bounded-density
identity on any measurable source-side chart piece pulls back by the readback
to finite-scalar domination by the theta reference on any supplied theta
superset.

Public Lean name:

```text
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn
```

## Inputs Used

- the concrete local source-chart image/readback package;
- a measurable source-side `chartPiece`;
- a theta superset `thetaSuperset` with `V ⊆ thetaSuperset`;
- an external source measure restricted to `chartPiece`;
- a supplied bounded-density identity against the chart-produced source
  reference;
- the generic chart-piece bounded-density readback domination theorem.

## Output

Assuming

```text
externalMeasure.restrict chartPiece =
  ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
    .restrict chartPiece
```

and `density <= c` almost everywhere for the restricted chart-produced source
reference, Lean proves:

```text
AEMeasurable readback (externalMeasure.restrict chartPiece)

Measure.map readback (externalMeasure.restrict chartPiece)
  <= c • thetaReference.restrict thetaSuperset.
```

## Nonclaims

The theorem assumes the density identity and bound.  It does not prove that an
original source prior or original volume has such a density, does not prove
source-image coverage, does not transport Haar measure, and does not prove
normal crossings, pole order, or RLCT extraction.
