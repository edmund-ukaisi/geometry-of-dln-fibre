# Reproduction - A2 with-following source-rank pointwise support

Status: pen-and-paper reproduction before Lean.

## Claim

For the enlarged Case 2 passive-theta endpoint source chart with independent
following factor, a chart-produced p.13 source family lies in Aoyagi's
source-rank stratum once the two residual-block rank equations are supplied:

```text
r + rank(F) = rEdge 0
r + rank(successor selected-entry matrix(yNext)) = rEdge 1.
```

Here `F` is the extra following-factor coordinate `z.2` in
`Case2PassiveThetaWithFollowingFactor`.

## Calculation

Let

```text
rawData = case2PassiveThetaWithFollowingFactorRetainedData(z),
data    = endpointTransport_e(rawData).
```

The endpoint source chart is the retained-passive p.13 source family attached
to `data`.  The general retained-passive source-rank lemma therefore reduces
the goal to proving, for `p = 0,1`,

```text
r + rank(data.C p) = rEdge p.
```

Endpoint transport preserves ranks of the `C p` blocks, so it is enough to
compute the ranks of `rawData.C 0` and `rawData.C 1`.

For `p = 0`, the enlarged construction stores the independent following
factor:

```text
rawData.C 0 = F.
```

Thus `rank(data.C 0) = rank(F)`, and the first supplied equation gives
`r + rank(data.C 0) = rEdge 0`.

For `p = 1`, the enlarged construction stores the displayed residual block
coming from the successor selected-entry matrix:

```text
rawData.C 1 =
  displayedPostPivotResidualBlock(sourceResidual(successorMatrix(yNext))).
```

The zero-extension/reindexing rank lemma gives

```text
rank(rawData.C 1) = rank(successorMatrix(yNext)).
```

So endpoint-transport rank preservation and the second supplied rank equation
give `r + rank(data.C 1) = rEdge 1`.

Passing these two equations to
`paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData_mem_sourceRankStratum_of_C_rank_add_eq`
proves source-rank membership.

## Local Image and Measure Wrappers

The existing local source-image package returns an open set `V` with

```text
detChart(retainedData z), readback(sourceChart z) = z,
sourceChart injective/continuous on V,
measurable(sourceChart '' V).
```

Applying the pointwise theorem for each `z in V` gives:

```text
if  r + rank(z.2) = rEdge 0
and r + rank(successorMatrix(z.1.yNext)) = rEdge 1,
then sourceChart z is in the source-rank stratum.
```

Therefore a uniform pair of rank equations on `V` gives

```text
sourceChart '' V subset sourceRankStratum.
```

For an arbitrary theta-side measure restricted to `V`, the same pointwise
membership holds almost everywhere if the two rank equations hold almost
everywhere on `thetaMeasure.restrict V`.  Since `sourceChart` is continuous on
`V`, it is a.e. measurable there; the generic
`measure_map_restrict_sourceRankStratum_eq_self_of_ae_mem` then gives support
of the pushed-forward chart-produced measure on the source-rank stratum.

## Boundary

This is only pointwise one-way support for chart-produced source families.  It
does not prove source-rank coverage, equality with a source-rank stratum,
finite atlas coverage, source-prior transport, Haar/Jacobian transport, normal
crossings, pole order, or RLCT extraction.  The local image and measure
wrappers are still one-way support statements for chart-produced objects.
