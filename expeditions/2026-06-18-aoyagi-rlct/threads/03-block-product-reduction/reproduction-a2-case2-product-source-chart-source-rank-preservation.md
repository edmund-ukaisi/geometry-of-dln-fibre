# Reproduction - A2 Case 2 product source-chart source-rank preservation

Date: 2026-07-01.

Status: pen-and-paper check for one-way source-rank preservation under the
concrete p.13 product source chart.

## Question

Assume the passive-theta endpoint source chart point has the Case 2 source-rank
data

```text
rank(totalMap) = r
r + card tau = rEdge 0
r + rank(successor selected-entry matrix) = rEdge 1.
```

After adding small p.13 regular coordinates `u`, does the product source chart
remain in the same source-rank stratum?

## Calculation

The passive-theta endpoint source chart is built from retained-passive
determinant-chart data.  Membership in the retained-passive local source is
equivalent to the fixed-base recursive determinant-chart predicate.  The
generic certificate constructor turns that recursive determinant-chart
predicate into a fixed-base product-reduction certificate.

The existing Case 2 source-rank theorem proves that the passive-theta source
chart lies in

```text
paperEndpointFixedBaseSourceRankStratum W2 B2 sourceChart r rEdge
```

from the three rank equations above.

For the product chart, Aoyagi's p.13 block calculation gives edge matrices of
the form

```text
[ Ctop  0 ]      [ I  F3 ]      [ I  0 ]
[ F2    C ]      [ 0  C  ]      [ F2 C ]
```

at the left endpoint, middle edges, and right endpoint respectively.  If
`det Ctop` is a unit, each matrix has rank

```text
r + rank(C_p) = rEdge p.
```

The generic theorem

```text
paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_sourceRankStratum
```

packages exactly this argument: base product-reduction certificate plus base
source-rank membership plus unit `det(Ctop(u))` implies product source-rank
membership.  Shrinking `u` to a small Euclidean ball around `0` supplies the
unit determinant condition because `Ctop(0) = I`.

## Lean Targets

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
case2PassiveThetaEndpointSourceChart_productReductionCertificate

exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_sourceRankStratum_of_base_rank
```

## Boundary

This is one-way source-rank membership for chart-produced points.  It does not
prove that all nearby source-rank points are chart-produced, that the source
rank stratum is open, or that any original prior/density/Jacobian, normal
crossing, pole-order, or RLCT statement holds.
