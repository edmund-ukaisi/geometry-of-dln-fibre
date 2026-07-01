# Statement Card - A2 Case 2 baseJ raw-image density handoff

## Claim

On the local Case 2 passive-theta determinant/pivot sector, let

```text
passiveSource = passiveMeasure.prod weightedBox
baseJ = passiveSource.withDensity jacobianDensity,
```

where `jacobianDensity` is Aoyagi's retained-passive formal raw-order product
determinant evaluated at the endpoint topology tuple.  If this theta-side
Jacobian density factors almost everywhere through the local raw-order map as a
raw density,

```text
jacobianDensity z = rawDensity (rawMap z)
```

with `rawDensity` a.e.-measurable for the raw-image measure, then

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (passiveSource.restrict V)).withDensity rawDensity.
```

Public Lean names:

```text
measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq

exists_open_subset_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_eq_withDensity_rawImage_of_jacobianDensity_ae_eq
```

## Inputs Used

- the local Case 2 passive-theta determinant/pivot sector theorem, to obtain an
  open `V subset G` where the endpoint tuple lies in the determinant chart and
  the raw-order map is continuous on `V`;
- the generic `withDensity` pushforward lemma for a density that factors
  through a measurable map;
- the explicit a.e. factorization and raw-density a.e.-measurability
  hypotheses.

## Output

Lean proves the exact raw-image identity

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (passiveSource.restrict V)).withDensity rawDensity.
```

This is a theorem about the actual raw-image measure
`Measure.map rawMap (passiveSource.restrict V)`.

## Nonclaims

This does not identify the raw-image measure with raw Haar restricted to the
raw-order source-recursive determinant chart.  It does not prove determinant
chart Haar transport from the passive-product theta measure, raw Haar
normalization, original source-prior transport, source-image coverage,
source-rank coverage, normal crossings, pole order, or RLCT extraction.
