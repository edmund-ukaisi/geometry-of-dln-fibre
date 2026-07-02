# Statement Card - A2 Case 2 with-following source-image automatic readback measurability

## Statement

Near any enlarged Case 2 determinant-sector point with nonzero selected pivot,
inside any prescribed open theta-neighborhood `G`, there is a smaller open set
`V` such that the with-following endpoint source chart is continuous and
injective on `V`, has measurable image, and has a pointwise readback left
inverse on `V`.

For any theta-domain reference measure `thetaReference`, any source-image
density `density`, and any scalar `c`, if

```text
density E <= c
```

a.e. for

```text
(Measure.map sourceChart (thetaReference.restrict V)).restrict
  (sourceChart '' V),
```

then

```text
Measure.map readback
  (((Measure.map sourceChart (thetaReference.restrict V)).withDensity density)
    .restrict (sourceChart '' V))
<= c * thetaReference.restrict V.
```

The readback a.e.-measurability for the chart-produced source-image reference
is generated internally from the local continuous injective chart and
left-inverse data.

## Lean Target

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointSourceChart_map_readback_withDensity_restrict_image_le_smul_of_continuousOn_injOn
```

## Inputs Used

- the with-following local source-chart package;
- `MeasurableSet V`, supplied by openness of the shrink;
- `ContinuousOn sourceChart V`;
- `Set.InjOn sourceChart V`;
- `readback (sourceChart z) = z` on `V`;
- the supplied local a.e. bound on the density.

## Nonclaims

No determinant-chart Haar equality, no endpoint Haar transport, no raw-order
Haar transport, no raw-map pushforward to Haar, no source-prior
identification, no density construction, no source-image coverage beyond the
actual local image, no Jacobian formula, no normal crossings, no pole order,
and no RLCT extraction.
