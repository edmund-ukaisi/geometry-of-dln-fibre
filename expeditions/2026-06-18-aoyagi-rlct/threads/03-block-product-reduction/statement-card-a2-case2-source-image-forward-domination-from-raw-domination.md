# Statement Card - A2 Case 2 source-image forward domination from raw domination

## Claim

On the usual local Case 2 determinant/punctured-sector shrink, forward
domination of the raw-order image by restricted raw Haar implies forward
domination of the concrete passive-theta source-image measure by restricted
original edge-family volume.

Expected public Lean name:

```text
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_le_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet_of_rawMap_le_smul_restrict_rawSource
```

## Statement Shape

For the local `V subset G`, for every `thetaReference`, raw Haar `rawHaar`,
and scalar `C`, if

```text
Measure.map rawMap (thetaReference.restrict V)
  <= C * rawHaar.restrict rawSourceSet,
```

then

```text
Measure.map sourceChart (thetaReference.restrict V)
  <= (C * cHaar) * originalVolume.restrict p13SourceSet.
```

Here `cHaar` is the existing tuple-side full-space Haar scalar

```text
((Measure.map rawLinearEquiv rawHaar)
  .addHaarScalarFactor (originalTupleVolume d)).
```

## Inputs Used

- The local two-stage raw-order/source-chart measure identity.
- A.e. measurability of the p.13 raw-order source chart on
  `rawHaar.restrict rawSourceSet`, obtained by agreement on `rawSourceSet`
  with the continuous fixed-basis raw-order tuple readout.
- `map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet`.

## Nonclaims

This is not raw-Haar identification or original-volume transport.  It gives
`sourceImage <= originalVolume`, not `originalVolume <= sourceImage`.  It does
not prove the readback domination required by the original-volume
finite-integral theorem, determinant-chart Haar transport, source-image
coverage, source-rank coverage, source-prior transport, normal crossings,
pole order, or RLCT extraction.
