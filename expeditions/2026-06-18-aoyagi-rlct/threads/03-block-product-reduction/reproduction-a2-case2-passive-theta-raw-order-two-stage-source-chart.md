# Reproduction - A2 Case 2 passive theta raw-order two-stage source chart

Date: 2026-06-30.

Status: pen-and-paper check before Lean.  This is a local source-chart
comparison, not Haar transport or source-prior construction.

## Question

The endpoint-sector pushforward theorems now name the image of
`case2PassiveThetaEndpointTopologyTuple`, but the residual-source handoff still
uses the directly chart-produced source family
`case2PassiveThetaEndpointSourceChart`.  Can we prove, locally on the same
punctured determinant sector, that the direct source chart is the raw-order
p.13 source chart applied to the raw-order version of the endpoint topology
tuple?

Answer: yes.  This is the concrete `Case2PassiveTheta` specialization of the
generic passive selected-entry raw-order bridge.

## Setup

Fix the p.13 endpoint data `W2, B2, U0, hU0`, the Case 2 indices
`n, S, J`, and endpoint equivalences `eNext, e`.  For a full passive theta
coordinate `theta`, set

```text
Y theta =
  case2PassiveThetaEndpointTopologyTuple n hS hcont hnext theta eNext e

rawMap theta =
  topologyTupleEdgeRawOrder (Y theta)

rawChart =
  paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W2 B2 U0 hU0

sourceChart theta =
  case2PassiveThetaEndpointSourceChart W2 B2 n hS hcont hnext hU0 eNext e theta
```

The selected-entry residual inverse readout is

```text
inverseReadout =
  case2PassiveThetaEndpointInverseReadout W2 B2 n hS hnext hU0 eNext e.
```

Assume the base point `z0` lies in the passive determinant sector and has
nonzero successor selected pivot.

## Calculation

The generic passive selected-entry construction internally obtains an open
neighborhood by intersecting a determinant-chart neighborhood with a
nonzero-pivot condition.  The concrete public theorem exports the consequences
needed downstream, not a standalone subset theorem for this `V`.  For
`theta in V`, the endpoint retained datum is

```text
retainedData theta =
  case2PassiveThetaEndpointRetainedData n hS hcont hnext theta eNext e.
```

The determinant-sector part gives

```text
Y theta = topologyTuple (retainedData theta)
```

inside `topologyTupleDetChartSet`.  Therefore applying raw order gives

```text
rawMap theta =
  topologyTupleEdgeRawOrder (topologyTuple (retainedData theta)).
```

The p.13 raw-order source chart is constructed to invert this raw-order
topology tuple back to the same retained-passive source family.  Hence on `V`

```text
rawChart (rawMap theta) = sourceChart theta.
```

The same local source-readback calculation gives

```text
sourceReadback (edgeMatrix (sourceChart theta)) = retainedData theta.
```

Since the pivot coordinate is nonzero on `V`, the selected-entry chart map and
`preimageOfPivotNeZero` are inverse at the chosen pivot.  The residual block
read through the source chart is exactly the residual-factor product of the
readback data, so

```text
inverseReadout (sourceChart theta) = theta.yNext.
```

For any theta-domain measure `sourceMeasure`, restricting it to `V` and using
the pointwise equality gives

```text
Measure.map (fun theta => rawChart (rawMap theta)) (sourceMeasure.restrict V)
  =
Measure.map sourceChart (sourceMeasure.restrict V).
```

When the endpoint topology-tuple and source-family targets carry the needed
Borel measurable structures, the generic bridge supplies the measurability
needed to reassociate the maps and gives the genuine two-stage presentation

```text
Measure.map rawChart
  (Measure.map rawMap (sourceMeasure.restrict V))
  =
Measure.map sourceChart (sourceMeasure.restrict V).
```

## Lean Target

Add the concrete specialization to

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Suggested public name:

```text
exists_open_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
```

## Nonclaims

This slice does not prove exact passive-sector Haar transport,
determinant-chart Haar transport, raw-order Haar transport, source-prior
transport, source-image equality, source-rank coverage, a passive-sector
Jacobian formula, normal crossings, pole order, or RLCT extraction.  It only
identifies, locally and pointwise, the direct source chart with the raw-order
source chart applied to the endpoint topology tuple, and records the resulting
restricted pushforward equality.
