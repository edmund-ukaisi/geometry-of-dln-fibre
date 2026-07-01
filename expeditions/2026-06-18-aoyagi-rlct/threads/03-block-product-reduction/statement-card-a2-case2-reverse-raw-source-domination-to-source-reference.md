# Statement Card - A2 Case 2 reverse raw-source domination to source reference

## Expected Lean Names

```text
exists_open_subset_formalProductMeasure_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap

exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_le_smul_sourceReference_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap
```

## Statement Shape

Return a local `V subset G` for the concrete Case 2 passive-theta raw-order and
endpoint source chart.  For every `thetaReference`, additive raw Haar measure
`rawHaar`, p.13 chart piece, and scalar `D`, assume

```text
rawHaar.restrict rawSourceSet
  <= D • Measure.map rawMap (thetaReference.restrict V).
```

The first theorem concludes

```text
formalProductMeasure.restrict chartPiece <= D • sourceRef,
```

provided `chartPiece subset p13SourceSet`.

The second theorem adds `MeasurableSet chartPiece` and concludes

```text
originalVolume.restrict chartPiece
  <= (cHaar^{-1} * D) • sourceRef.
```

## Inputs Used

- The local Case 2 two-stage identity
  `Measure.map rawChart (Measure.map rawMap _) = Measure.map sourceChart _`.
- Raw-image support in `rawSourceSet`.
- A.e. measurability of the p.13 raw-order source chart on raw-source
  restrictions.
- The p.13 formal-product measure identity.
- The p.13 original-volume/formal-product inverse Haar scalar bridge.

## Nonclaims

The reverse raw-source domination remains supplied.  The statement does not
prove determinant-chart Haar transport, exact raw-Haar pushforward, source
coverage, source-rank coverage, original source-prior transport, Haar scalar
normalization, normal crossings, pole order, or RLCT extraction.
