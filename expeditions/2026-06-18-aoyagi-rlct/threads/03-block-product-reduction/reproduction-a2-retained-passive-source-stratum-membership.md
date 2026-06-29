# A2 retained-passive source-stratum membership

## Question

The previous edge-rank bridge computed retained-passive edge ranks, but it
deliberately did not prove membership in Aoyagi's source-rank stratum.  The
next pointwise bridge is to package exactly the data needed for membership,
without proving any local coverage or exact-rank openness.

## Source-stratum fields

Aoyagi's fixed-base source-shaped rank stratum is the set of source edge
families satisfying three fields:

```text
rank(total product) = r,
rank(edge p) = rEdge p for every p,
r <= rEdge p for every p.
```

For a retained-passive datum `data`, the realised p.13 source family

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W B U0 hU0 data
```

has fixed-base edge matrices exactly `data.edgeMatrix`.  Therefore, if the
product-rank equality, the edge-matrix rank equalities, and the inequalities
are supplied, membership in the source-shaped rank stratum is a direct
constructor.

## Residual-rank form

On the determinant chart, the retained-passive edge-rank formula gives

```text
rank(data.edgeMatrix p) = card(Fin (finrank K U0)) + rank(data.C p).
```

The endpoint complement certificate identifies

```text
card(Fin (finrank K U0))
  = finrank K U0
  = rank(total product)
  = r.
```

Thus, if

```text
rank(data.C p) = rEdge p - r
```

and `r <= rEdge p`, then

```text
rank(data.edgeMatrix p) = r + (rEdge p - r) = rEdge p.
```

Equivalently, callers may provide the non-truncated form

```text
r + rank(data.C p) = rEdge p.
```

This implies both the residual-rank subtraction statement and the inequality.

## Endpoint transport

Endpoint transport reindexes each retained-passive residual block:

```text
(data.endpointTransport e).C p
  = (data.C p).submatrix (e p.succ).symm (e p.castSucc).symm.
```

Reindexing rows and columns by equivalences preserves matrix rank, so

```text
rank((data.endpointTransport e).C p) = rank(data.C p).
```

## Case 2 specialization

For the explicit continuing Case 2 selected-entry datum before endpoint
transport:

```text
rank(C 0) = card tau,
rank(C 1) = rank(case2SuccessorSelectedEntryMatrix ...).
```

Endpoint transport preserves these residual-block ranks.  Hence the
endpoint-transported Case 2 p.13 source family lies in the source-shaped rank
stratum when the caller supplies

```text
rank(total product) = r,
r + card tau = rEdge 0,
r + rank(case2SuccessorSelectedEntryMatrix ...) = rEdge 1.
```

The second equality is intentionally not a numerical rank computation for the
successor selected-entry matrix.

## Boundary

This is pointwise membership for a constructed source family under explicit
rank data.  It does not prove local source-rank coverage, selected-entry image
equality, exact-rank openness, source-prior or Jacobian transport, analytic
atlas construction, normal crossings, pole order, or RLCT.
