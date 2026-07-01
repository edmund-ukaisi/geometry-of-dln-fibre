# Statement Card - A2 Case 2 Passive-theta Source-image p.13 Source-set Support

## Claim

For the local passive-theta endpoint chart returned around a determinant-sector,
nonzero-pivot base point, the actual chart image lies in the named p.13
retained-passive source edge-family set.

The returned local package includes:

```text
V open
z0 in V
V subset G
forall z in V, (retainedData z).detChart
forall z in V, readback (sourceChart z) = z
Set.InjOn sourceChart V
ContinuousOn sourceChart V
MeasurableSet (sourceChart '' V)
forall z in V, sourceChart z in p13SourceSet
forall E in sourceChart '' V, E in p13SourceSet
```

## Public Lean Name

```text
exists_open_subset_measurableSet_case2PassiveThetaEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
```

## Inputs Used

- the local passive-theta source-image inverse theorem;
- the determinant-chart membership returned on the smaller open set;
- `paperEndpointFixedBaseRetainedPassiveP13SourceChart_mem_sourceEdgeFamilySet`;
- the definition of `case2PassiveThetaEndpointSourceChart`;
- elementary unpacking of image membership.

## Nonclaims

The theorem does not prove source coverage, image equality with the p.13 source
set, source-rank coverage, original-prior transport, Haar scalar normalization,
normal crossings, pole order, RLCT extraction, or any measure comparison.
