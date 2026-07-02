# Reproduction - A2 Case 2 with-following endpoint active readout

Date: 2026-07-02.

Status: finite endpoint-coordinate readout reproduced and formalised.  This
note does not claim determinant-chart Haar transport, raw-map pushforward,
source-image coverage, normal crossings, pole order, or RLCT extraction.

## Source Boundary

Aoyagi's Case 2 calculation, PDF pp. 19-21, fixes one selected pivot in the
successor residual block and writes the post-pivot two-edge family with:

```text
C 1 = displayed post-pivot residual block,
C 0 = displayed post-pivot following factor.
```

In the enlarged Lean coordinate model the independent following factor is
stored as a matrix `F`, converted to a normalized free `C'` by

```text
case2DisplayedPostPivotFreeCprimeOfFollowingFactor ... F.
```

The endpoint topology tuple

```text
Y z = case2PassiveThetaWithFollowingFactorEndpointTopologyTuple ... z
```

already contains the endpoint-transported retained data built from the
selected-entry chart.  Therefore the next coordinate readout must not apply
the selected-entry chart a second time.

## Calculation

Let

```text
z = (theta, F)
```

be an enlarged passive-theta coordinate.  Pull an endpoint topology tuple back
to the untransported retained-coordinate domains by applying
`ofTopologyTuple` and then endpoint transport by the inverse equivalences.
For `T = Y z`, this gives exactly

```text
case2PassiveThetaWithFollowingFactorRetainedData ... z eNext.
```

The active `C` factors then read as follows.

First, the tail factor is

```text
C 1 =
  case2DisplayedPostPivotResidualBlock
    (case2SuccessorSelectedEntrySourceResidual ... theta.yNext eNext).
```

Reading this residual block by the residual-coordinate equivalence gives

```text
SelectedEntrySignedBox.CenterCoord.chartMap pivotNext theta.yNext.
```

Second, the head factor is

```text
C 0 =
  case2DisplayedPostPivotFreeFollowingFactor
    (case2DisplayedPostPivotFreeCprimeOfFollowingFactor ... F)
  = F.
```

Thus the active readout of the endpoint tuple is exactly

```text
activeReadout (Y z)
  = ((theta.passiveFields, chartMap pivotNext theta.yNext), F).
```

No pivot-nonzero hypothesis is needed for this readout: it reads the charted
coordinates already present in `C 1`.  The pivot-nonzero hypothesis only
enters the inverse readback that recovers the uncharted source coordinates.

## Measure Corollary

Composing `Y` with this active readout gives the same source-coordinate map as
the active selected-entry chart:

```text
z |-> ((z.1.1, chartMap pivotNext z.1.yNext), z.2).
```

Therefore the already-formalised source-coordinate product COV gives

```text
Measure.map (activeReadout o Y) referenceSource
  =
(passiveRef.prod (volume.restrict (chartMap pivotNext '' signedBoxSet Rres))).prod
  followingRef.
```

This is a readout marginal of the endpoint tuple, not a proof that the
endpoint image measure is determinant-chart Haar measure.

