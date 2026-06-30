# Statement Card - A2 Case 2 Passive Theta Endpoint Local Injectivity and Measurable Image

Date: 2026-06-30.

## Lean Claim

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

New public names:

```text
exists_open_case2PassiveThetaEndpointTopologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
exists_open_case2PassiveThetaEndpointTopologyTuple_sourceChart_injOn
exists_open_measurableSet_case2PassiveThetaEndpointSectorSet
```

## Mathematical Content

The first theorem is the pointwise, non-measure version of the raw-order
source-chart bridge for the concrete full `Case2PassiveTheta` endpoint topology
tuple.  It returns a local open neighborhood on which

```text
rawChart (topologyTupleEdgeRawOrder (Y z)) = sourceChart z
```

and keeps the existing source-readback and selected-entry inverse-readout
identities.

The second theorem combines that pointwise raw-order bridge with the local
source-chart readback left inverse.  It returns one open neighborhood `V` of a
determinant-sector, nonzero-pivot base point such that both maps are injective
on `V`:

```text
Set.InjOn sourceChart V
Set.InjOn Y V
```

where

```text
Y z = case2PassiveThetaEndpointTopologyTuple ... z eNext e.
```

The third theorem applies `MeasurableSet.image_of_continuousOn_injOn` under
explicit Polish/Borel hypotheses on the theta coordinate domain and opens
measurable/T2 hypotheses on the endpoint topology-tuple target.  It returns an
open neighborhood `V` such that

```text
MeasurableSet (case2PassiveThetaEndpointSectorSet ... V).
```

## Proof Source

Pen-and-paper reproduction:

```text
reproduction-a2-case2-passive-theta-endpoint-local-injectivity-measurable-image.md
```

The proof is local coordinate algebra plus Lusin-Souslin.  Source-chart
injectivity follows by applying the readback left inverse.  Endpoint
topology-tuple injectivity follows because equality of endpoint topology
tuples gives equality of raw-order tuples, and locally the raw-order source
chart recovers the direct source chart.  Measurability follows from continuity
of `case2PassiveThetaEndpointTopologyTuple` and local injectivity.

## Nonclaims

This slice does not prove global endpoint-sector measurability, source-image
equality, source-rank coverage, exact passive-sector Haar transport,
determinant-chart Haar transport, raw-order Haar transport, source-prior
comparison, normal crossings, pole order, or RLCT extraction.

## Verification So Far

Passed before review:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
```

The focused build replayed existing files with pre-existing warnings outside
this slice.

