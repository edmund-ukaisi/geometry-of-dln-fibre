# Reproduction - A2 Case 2 produced source-rank point readout

Date: 2026-06-29.

Status: pen-and-paper reproduction for a narrow Lean package theorem.

## Question

The current Case 2 point-production theorem produces a retained-passive
p.13 local-source point whose residual-coordinate readout is a prescribed
selected-entry center value, provided the selected pivot value is nonzero.

Can the same produced point also be shown to lie in the fixed-base source-rank
stratum, using the edge-rank equations for that same produced point?

Answer: yes.  This is pointwise source-rank membership for the same produced
point; it is not source-rank coverage or image equality.

## Source Calculation

Aoyagi's p.13 retained-passive coordinates split each edge around a fixed
rank-`r` base product.  On a determinant chart, the source-recursive edge
family has edge-rank increments equal to the ranks of the retained residual
blocks `C_p`.  In the two-edge continuing Case 2 selected-entry specialization
after endpoint transport:

```text
rank(edge 0) = r + card tau,
rank(edge 1) = r + rank(successor selected-entry matrix).
```

Therefore, for the produced coordinate

```text
yNext = preimageOfPivotNeZero pivotNext value,
```

it suffices to supply

```text
finrank range(paperTotalMap W2 B2) = r,
r + card tau = rEdge 0,
r + rank(case2SuccessorSelectedEntryMatrix ... yNext ...) = rEdge 1.
```

Then the endpoint-transported Case 2 source edge family produced from this
selected-entry coordinate lies in `paperEndpointFixedBaseSourceRankStratum`.
The rank equation is deliberately pointwise.  A uniform equation for all
selected-entry coordinates is stronger than this point-production theorem
needs and is not the intended claim here.

Separately, the existing fixed-pivot selected-entry inverse gives, for a
center value `value` with nonzero selected pivot, coordinates

```text
yNext = preimageOfPivotNeZero pivotNext value
```

with

```text
chartMap pivotNext yNext = value.
```

The existing local-source/readout theorem applies to exactly this `yNext`, so
the same source family lies in the p.13 local source and its fixed-base
residual-coordinate map is the prescribed value.

## Lean Target

Add the package theorem

```text
exists_case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum_and_localSource_and_residualBlockCoordinateMap_eq_value_of_pivot_ne_zero
```

in `RetainedPassiveCase2LocalJacobianMeasure.lean`.

It should choose the same fixed-pivot inverse coordinate as the existing
local-source/readout theorem, use the local-source/readout bridge for that
coordinate, and reuse

```text
case2EndpointTransport_sourceEdgeFamilyOfData_mem_sourceRankStratum
```

for source-rank membership with the pointwise edge-1 rank equation.

## Nonclaims

This theorem does not prove source-rank coverage, selected-entry image
equality, exact-rank openness, successor-rank arithmetic, source-prior
transport, Jacobian compatibility, normal crossings, pole order, or RLCT.
