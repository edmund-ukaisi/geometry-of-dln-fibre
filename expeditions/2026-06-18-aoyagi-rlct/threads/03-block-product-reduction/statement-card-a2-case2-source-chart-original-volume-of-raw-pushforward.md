# Statement Card - A2 Case 2 source-chart original-volume identity from raw pushforward

## Claim

On the local Case 2 passive-theta endpoint determinant/pivot sector, if the
passive-theta raw-order map sends the restricted theta reference measure to
the raw-order source-recursive restriction of a raw Haar measure, then the
concrete passive-theta endpoint source chart sends the same theta reference
to original edge-family volume restricted to the named p.13 source edge-family
set, up to the existing full-space Haar scalar.

Public Lean names:

```text
exists_open_subset_measure_map_case2PassiveThetaEndpointSourceChart_eq_smul_originalEdgeFamilyVolume_restrict_sourceEdgeFamilySet_of_rawMap_eq_restrict_rawSource

exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_eq_withDensity_invHaar_sourceReference_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
```

## Inputs Used

- the local Case 2 raw-order/source-chart equality;
- the concrete raw-order density transport theorem with density `1`;
- the previously formalized raw-order p.13-coordinate volume bridge;
- an explicit raw-pushforward hypothesis:

```text
Measure.map rawMap (thetaReference.restrict V)
=
rawHaar.restrict topologyTupleRawOrderSourceRecursiveDetChartSet.
```

## Output

Lean should prove:

```text
Measure.map sourceChart (thetaReference.restrict V)
=
cHaar • originalEdgeFamilyVolume.restrict p13SourceSet
```

where

```text
cHaar =
  (Measure.map paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
    rawHaar).addHaarScalarFactor originalTupleVolume.
```

It should also prove the chart-piece inverse-density corollary: for any
measurable `chartPiece subset p13SourceSet`,

```text
originalEdgeFamilyVolume.restrict chartPiece
=
  ((Measure.map sourceChart (thetaReference.restrict V)).withDensity
    (fun _ => cHaar^-1)).restrict chartPiece
```

with the tautological a.e. bound

```text
fun _ => cHaar^-1 <= cHaar^-1
```

over the restricted source-image reference.

## Nonclaims

This does not prove the raw-pushforward hypothesis.  It does not identify
the passive-theta raw map with raw Haar, prove determinant-chart Haar
transport, normalize the Haar scalar to `1`, prove original source-prior
transport, source-image coverage, source-rank coverage, normal crossings,
pole order, or RLCT extraction.

## Status

Lean file:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean
```

The two public theorems are sorry-free and axiom-clean with footprint
`[propext, Classical.choice, Quot.sound]`.
