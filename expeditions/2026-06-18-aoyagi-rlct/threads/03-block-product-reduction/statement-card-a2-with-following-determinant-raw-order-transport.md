# Statement card - A2 with-following determinant/raw-order transport

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawImageHandoff.lean
```

Names:

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_le_smul_rawHaar_restrict_rawSource_of_endpointTopologyTuple_restrict_le_smul_detHaar
exists_open_subset_rawHaar_restrict_rawSource_le_smul_measure_map_case2PassiveThetaWithFollowingFactor_rawMap_baseJ_restrict_of_detHaar_restrict_le_smul_endpointTopologyTuple
```

The exported constants are under:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData
```

## Claim

After shrinking inside a prescribed open neighborhood `G` of a Case 2
with-following passive-theta point, the retained-passive raw-order
change-of-variables theorem transports supplied determinant-chart domination
through the with-following endpoint map.

Forward direction:

```text
Measure.map Y (sourceMeasure.restrict V)
  <= c * rawHaar.restrict rawDetChart
```

implies:

```text
Measure.map rawMap (baseJ.restrict V)
  <= c * rawHaar.restrict rawSourceSet.
```

Reverse direction:

```text
rawHaar.restrict rawDetChart
  <= c * Measure.map Y (sourceMeasure.restrict V)
```

implies:

```text
rawHaar.restrict rawSourceSet
  <= c * Measure.map rawMap (baseJ.restrict V).
```

Here:

```text
baseJ = sourceMeasure.withDensity jacobianDensity
jacobianDensity z =
  ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z))
rawMap z = topologyTupleEdgeRawOrder (Y z).
```

## Proved

Both directions use the with-following endpoint shrink to work inside the
retained-passive determinant chart.  The endpoint map `Y` is a.e. measurable by
continuity, the determinant-side formal product density is a.e. measurable on
the determinant chart, and `topologyTupleEdgeRawOrder` is a.e. measurable after
restriction to that chart.

The substantive mathematical input is the retained-passive raw-order COV
identity:

```text
Measure.map Phi ((rawHaar.restrict rawDetChart).withDensity formalDensity)
  = rawHaar.restrict rawSourceSet.
```

The forward theorem applies the generic weighted pushforward domination lemma
from left to right.  The reverse theorem applies the corresponding reverse
domination lemma from the determinant Haar reference to the raw-source Haar
reference.

## Assumed

The determinant-side domination is still an explicit hypothesis in each
direction.  The source measure is an arbitrary measure on the enlarged
with-following theta domain.

The theorems assume the usual local Case 2 base data:

- the base point lies in the with-following determinant sector;
- the selected pivot at the base point is nonzero;
- `G` is open and contains the base point;
- the standard finite-dimensional/measurable-space instances for the
  with-following theta and retained-passive topology tuple targets.

## Cited

None.

## Deferred

No determinant-chart Haar domination/equality is proved.  No source-prior or
original-prior transport, no exact raw-Haar pushforward, no raw-Haar
normalization, no p.13 source-image coverage, no source-rank coverage, no
normal crossings, no pole order, and no RLCT extraction is proved.

## Status

Focused module build, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, direct axiom probes, and xhigh
review passed.  The two declarations report
`[propext, Classical.choice, Quot.sound]`.  Xhigh reviewer
`Ramanujan the 2nd` passed with no findings.
