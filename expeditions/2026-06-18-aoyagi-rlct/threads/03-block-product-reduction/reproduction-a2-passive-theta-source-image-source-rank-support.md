# Reproduction - A2 passive-theta source-image source-rank support

Date: 2026-06-30.

## Goal

For the concrete passive-theta endpoint source chart

```text
sourceChart(theta) =
  case2PassiveThetaEndpointSourceChart W2 B2 n hS hcont hnext hU0 eNext e theta,
```

prove a one-way source-rank support statement for the already constructed
local source image:

```text
sourceChart '' V subset sourceStratum.
```

The source stratum is

```text
paperEndpointFixedBaseSourceRankStratum W2 B2 id r rEdge.
```

The statement is conditional on explicit rank equations.  It must not be read
as coverage of the source-rank stratum or equality with the image.

## Calculation

Let

```text
data(theta) =
  case2PassiveThetaEndpointRetainedData n hS hcont hnext theta eNext e.
```

The source chart is exactly the fixed-base retained-passive p.13 source edge
family of this datum:

```text
sourceChart(theta) =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W2 B2 U0 hU0
    data(theta).
```

On the local determinant-chart domain, `data(theta).detChart` holds.  The
retained-passive edge-rank formula gives

```text
rank(edge_p) = r + rank(data(theta).C p)
```

once the base product rank is

```text
finrank range(paperTotalMap W2 B2) = r.
```

For the Case 2 passive-theta retained datum, the two residual ranks are the
displayed Case 2 ranks:

```text
rank(data(theta).C 0) = |tau|,
rank(data(theta).C 1) =
  rank(case2SuccessorSelectedEntryMatrix n hS hnext theta.yNext eNext).
```

The first identity is the rank of the free following-factor block.  The second
identity is the rank of the displayed successor residual block.  Endpoint
transport does not change the ranks of the stored `C` blocks.

Therefore the explicit equations

```text
r + |tau| = rEdge 0,
r + rank(case2SuccessorSelectedEntryMatrix n hS hnext theta.yNext eNext)
  = rEdge 1
```

give exact edge ranks `rEdge 0` and `rEdge 1`.  The retained-passive source
rank constructor then proves

```text
sourceChart(theta) in sourceStratum.
```

For image support, if `E in sourceChart '' V`, choose `theta in V` with
`E = sourceChart(theta)`.  The pointwise membership above applies at this
`theta`, provided the successor-rank equation holds at every point of `V`.

For measure support, let

```text
mu = Measure.map sourceChart (thetaMeasure.restrict V).
```

The local image theorem supplies `ContinuousOn sourceChart V`, hence
`sourceChart` is a.e. measurable for `thetaMeasure.restrict V`.  If the
successor-rank equation holds almost everywhere for `thetaMeasure.restrict V`,
then `sourceChart(theta) in sourceStratum` almost everywhere.  Since the
source-rank stratum is measurable for the identity edge-family map, restricting
`mu` to the stratum does not change it:

```text
mu.restrict sourceStratum = mu.
```

## Boundary

This proves only one-way support of chart-produced source points and
chart-produced pushed-forward measures on a named source-rank stratum.  It
does not prove source-rank coverage, source-image equality with the stratum,
openness of the exact-rank condition, original source-prior transport,
determinant-chart or raw-order Haar transport, normal crossings, pole order,
or RLCT extraction.
