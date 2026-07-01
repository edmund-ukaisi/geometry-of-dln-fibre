# Statement Card - A2 Case 2 original-volume/source-image domination from formal-product domination

## Expected Lean Name

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_same_shrink_of_formalProductMeasure_le_smul_sourceReference
```

## Statement Shape

Return a local `V subset G` for the concrete Case 2 passive-theta endpoint
source chart such that `sourceChart '' V` is measurable and lies in the p.13
source edge-family set.  For every additive raw Haar measure `m`, every
`thetaReference`, measurable `chartPiece`, and scalar `D`, if

```text
chartPiece subset sourceChart '' V
muP13.restrict chartPiece <= D • sourceRef
```

where

```text
sourceRef := Measure.map sourceChart (thetaReference.restrict V)
```

and `muP13` is the p.13 formal-product raw-order chart measure, then

```text
originalVolume.restrict chartPiece
  <= (cHaar^{-1} * D) • sourceRef.
```

## Inputs Used

- Local Case 2 source-chart image support in the p.13 source edge-family set.
- The p.13 formal-product/original-volume inverse-scalar chart-piece bridge.
- Elementary transitivity of scalar measure domination.

## Nonclaims

The formal-product/source-image domination hypothesis remains supplied.  This
does not prove raw-Haar transport, source-image coverage beyond the returned
actual image, source-rank coverage, original source-prior transport, Haar
scalar normalization, normal crossings, pole order, or RLCT extraction.
