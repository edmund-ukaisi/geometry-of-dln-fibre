# A2 Case 2: reverse raw-source domination from a lower source-density bound

Status: reproduced and formalised in Lean.

## Question

The finite-integral wrapper now needs the hypothesis

```text
rawReference <= D * Measure.map rawMap (coordinateSourceMeasure.restrict V),
D < infinity.
```

In the concrete Case 2 notation,

```text
coordinateSourceMeasure = baseJ.withDensity sourceDensity.
```

Assume a future geometric theorem supplies the base comparison

```text
rawReference <= D0 * Measure.map rawMap (baseJ.restrict V),
```

and the source density is bounded below on the same source shrink:

```text
epsilon <= sourceDensity theta
```

for `baseJ.restrict V`-a.e. `theta`, with `epsilon` nonzero and finite.

## Calculation

The lower density bound gives

```text
epsilon * baseJ.restrict V
  <= (baseJ.withDensity sourceDensity).restrict V.
```

Mapping this domination by `rawMap` gives

```text
epsilon * Measure.map rawMap (baseJ.restrict V)
  <= Measure.map rawMap ((baseJ.withDensity sourceDensity).restrict V).
```

Since `epsilon` is nonzero and finite, scalar inversion gives

```text
Measure.map rawMap (baseJ.restrict V)
  <= epsilon^{-1} *
     Measure.map rawMap ((baseJ.withDensity sourceDensity).restrict V).
```

Composing with the base raw domination yields

```text
rawReference
  <= (D0 * epsilon^{-1}) *
     Measure.map rawMap ((baseJ.withDensity sourceDensity).restrict V).
```

If `D0 < infinity`, then `D0 * epsilon^{-1} < infinity`.

## Boundary

This adapter does not prove the base raw domination, the lower bound for
`sourceDensity`, determinant-chart Haar transport, source-image coverage,
source-rank coverage, original source-prior transport, normal crossings, pole
order, or RLCT extraction.  It only isolates the elementary measure-theoretic
bookkeeping needed after those local hypotheses are supplied.

## Lean Landing

The generic adapter is

```text
measure_le_smul_map_restrict_withDensity_of_le_smul_map_restrict_of_ae_le
```

in `lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`.

The concrete Case 2 wrapper is

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean`.

It first uses the concrete reverse `baseJ` raw-source theorem

```text
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
```

and then applies the lower-density adapter with
`coordinateSourceMeasure = baseJ.withDensity sourceDensity`.
