# Statement Card - A2 Case 2 reverse raw-source density lower adapter

## Expected Lean Names

```text
smul_restrict_le_restrict_withDensity_of_ae_le
measure_le_inv_smul_of_smul_le
measure_le_smul_of_le_smul_of_smul_le
measure_le_smul_map_restrict_withDensity_of_le_smul_map_restrict_of_ae_le
weighted_map_ref_le_smul_map_comp_withDensity_comp_of_le_smul_map

exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple

exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveTheta_rawMap_coordinateSourceMeasure_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

## Statement Shape

The generic measure lemma says that if

```text
target <= D • Measure.map rawMap (base.restrict V)
```

and a density satisfies

```text
epsilon <= density
```

`base.restrict V`-a.e., with `epsilon` nonzero and finite, then

```text
target
  <= (D * epsilon^{-1}) •
     Measure.map rawMap ((base.withDensity density).restrict V).
```

The concrete Case 2 theorem chooses the same local `V subset G` as the reverse
`baseJ` raw-source theorem.  Under the explicit determinant-side reverse
domination

```text
rawHaar.restrict rawDetChart
  <= Cdet • Measure.map Y (passiveSource.restrict V),
```

the explicit finiteness hypothesis `Cdet < infinity`, and the explicit lower
bound

```text
epsilon <= sourceDensity z
```

for `baseJ.restrict V`-a.e. `z`, it concludes

```text
(Cdet * epsilon^{-1}) < infinity
```

and

```text
rawHaar.restrict rawSourceSet
  <= (Cdet * epsilon^{-1}) •
     Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

Here `coordinateSourceMeasure = baseJ.withDensity sourceDensity`.

## Inputs Used

- Reverse `baseJ` raw-source domination from determinant-side reverse
  domination.
- The weighted reverse map-reference adapter
  `weighted_map_ref_le_smul_map_comp_withDensity_comp_of_le_smul_map`.
- The elementary scalar inversion lemma for `epsilon • μ <= ν`.
- Local measurability of `V`, supplied by `IsOpen V`.
- The lower bound for `sourceDensity`, a.e. with respect to `baseJ.restrict V`.
- A.e. measurability of `rawMap` for the coordinate source measure, obtained
  from absolute continuity with respect to `baseJ.restrict V`.

## Nonclaims

The determinant-side reverse domination and the source-density lower bound are
both supplied hypotheses.  The statement does not prove determinant-chart Haar
transport, exact raw-Haar pushforward, raw-Haar normalization, source-image
coverage, source-rank coverage, original source-prior transport, normal
crossings, pole order, or RLCT extraction.
