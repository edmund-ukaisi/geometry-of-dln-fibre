# Statement Card - A2 formal-product domination from determinant domination and source-density lower bound

## Expected Lean Name

```text
exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_coordinateSourceReference_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower
```

## Statement Shape

For the concrete Case 2 passive-theta chart, the theorem returns an open
neighborhood `V` of the base point with `V subset G`.  On this same `V`, for
every additive raw Haar measure, chart piece, and finite determinant scalar,
it assumes:

```text
chartPiece subset p13SourceSet,

rawHaar.restrict rawDetChart
  <= Cdet * Measure.map Y (passiveSource.restrict V),

Cdet < infinity,

forall-a.e. z with respect to baseJ.restrict V,
  epsilon <= sourceDensity z,

epsilon != 0,
epsilon != infinity.
```

It concludes, with `Ddet = Cdet * epsilon^{-1}`:

```text
Ddet < infinity,

formalProductMeasure.restrict chartPiece
  <= Ddet *
       Measure.map sourceChart (coordinateSourceMeasure.restrict V).
```

Here:

```text
coordinateSourceMeasure = baseJ.withDensity sourceDensity,
sourceDensity z = sourceImageDensity (sourceChart z).
```

## Inputs Used

- `exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap`
  consumes reverse raw-source domination and gives formal-product domination.
- `exists_open_subset_case2PassiveTheta_sourceChart_rawMap_coordinateSourceMeasure_reverse_domination_package_of_detHaar_restrict_le_smul_endpointTopologyTuple_sourceDensity_lower`
  produces reverse raw-source domination from determinant-side reverse
  domination and a source-density lower bound.
- `restrict_restrict_eq_self_of_subset` identifies
  `(coordinateSourceMeasure.restrict V).restrict Vformal` with
  `coordinateSourceMeasure.restrict V` because `V subset Vformal`.

## Nonclaims

The theorem does not prove determinant-chart Haar transport, source-density
positivity, source-density identification, original source-prior transport,
source-image/source-rank coverage, normal crossings, pole order, or RLCT
extraction.  It is a conditional composition theorem only.
