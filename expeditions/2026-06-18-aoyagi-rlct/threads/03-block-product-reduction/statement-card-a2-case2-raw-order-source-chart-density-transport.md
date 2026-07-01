# Statement Card - A2 Case 2 raw-order source-chart density transport

## Claim

On the local Case 2 passive-theta endpoint determinant/pivot sector, the
raw-order p.13 source chart and the concrete passive-theta endpoint source
chart give the same weighted source-side measure when the raw density is
placed on the `rawMap` pushforward of the restricted theta reference.

Public Lean names:

```text
measure_map_withDensity_comp_of_aemeasurable

measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict

exists_open_subset_measure_map_case2PassiveThetaEndpoint_rawOrderSourceChart_withDensity_eq_sourceChart_withDensity
```

## Inputs Used

- the relative Case 2 raw-order/source-chart wrapper;
- the local open shrink `V` around a determinant-sector, nonzero-pivot base
  point;
- a theta reference measure;
- a raw density a.e.-measurable for
  `Measure.map rawMap (thetaReference.restrict V)`;
- a.e. measurability of `rawMap` for `thetaReference.restrict V`;
- the generic `withDensity` pushforward lemma.

## Output

For the local `V`, Lean proves:

```text
Measure.map rawChart
  ((Measure.map rawMap (thetaReference.restrict V)).withDensity rawDensity)
=
Measure.map sourceChart
  ((thetaReference.withDensity
    (fun theta => rawDensity (rawMap theta))).restrict V).
```

The theorem also records the pointwise local equality

```text
rawChart (rawMap theta) = sourceChart theta
```

for `theta ∈ V`.

## Nonclaims

This does not identify the `rawMap` pushforward with determinant-chart Haar
measure or raw-order Haar measure.  It does not prove an original source-prior
density identity, source-image coverage, source-rank coverage, normal
crossings, pole order, or RLCT extraction.
