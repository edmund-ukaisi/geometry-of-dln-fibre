# Reproduction - A2 Case 2 endpoint equivalences from cardinalities

Date: 2026-06-28.

Status: reproduced; Lean targets selected.

## Target

The Case 2 endpoint-transport local-measure wrappers currently require two
families of equivalences:

```text
eNext : tau ~= Case2ResidualColIndex n S (J + 1)
e q   : case2PostPivotTwoEdgeDomain n S J tau q ~= kappa q.
```

The present rung constructs these equivalences only from finite cardinality
equalities.  It does not identify a preferred order, label, pivot, or
geometric source of the bijections.

## Finite equivalence construction

For any finite types `A` and `B`, a cardinality equality

```text
Fintype.card A = Fintype.card B
```

gives a noncanonical equivalence

```text
A ~= B
```

by `Fintype.equivOfCardEq`.

Apply this first to the successor right endpoint:

```text
hNext :
  Fintype.card tau =
    Fintype.card (Case2ResidualColIndex n S (J + 1)).
```

This yields

```text
eNext : tau ~= Case2ResidualColIndex n S (J + 1).
```

Separately, suppose that each endpoint of the displayed Case 2 two-edge family
has the same cardinality as a target endpoint family `kappa`:

```text
hEndpoints q :
  Fintype.card (case2PostPivotTwoEdgeDomain n S J tau q) =
    Fintype.card (kappa q).
```

Then `Fintype.equivOfCardEq (hEndpoints q)` gives the endpoint equivalence at
that `q`.  Keeping `hNext` separate is necessary: the endpoint family equality
at `q = 0` identifies `tau` with `kappa 0`, not with the successor residual
column index.

Lean target:

```lean
case2EndpointTransportEquivs_of_card_eq
```

## Fixed-base endpoint complement cardinality

For fixed-base p.13 source data, the endpoint-compatible complement index at
`q` is

```text
throughSubspaceEndpointComplementIndex
  (reverseVertex W) (reverseEdge W B) U0 q
```

and its cardinality is already known to be

```text
finrank (reverseVertex W q) - finrank U0.
```

The source-data package supplies:

```text
sourceData.dimensionConvention q.rev :
  H (q.rev.val + 1) = finrank (W q.rev),

sourceData.localSourceCertificate.source_basepoint.1 :
  finrank (range (paperTotalMap W B)) = r.
```

The chosen complement certificate also gives

```text
finrank U0 = finrank (range (paperTotalMap W B)).
```

Since `reverseVertex W q` is `W q.rev`, these identities rewrite the endpoint
complement cardinality to

```text
H (q.rev.val + 1) - r.
```

Lean target:

```lean
PaperEndpointFixedBaseRegularCoordinateSourceData.endpointComplementIndex_card_eq_H_rev_sub_rank
```

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** Noncanonical finite endpoint equivalences from
explicit cardinality equalities; source-data endpoint complement cardinality
in terms of the displayed width function `H` and rank `r`.

**Assumed.** The cardinality equalities in the Case 2 equivalence constructor.
For the fixed-base helper, the existing source-data package and its base
product-rank certificate.

**Cited.** None.

**Deferred.** Construction of canonical or label-preserving endpoint
equivalences; proof that `tau` is the geometrically correct source endpoint;
selected-entry or pivot-order preservation; source-chart membership; measure
transport; Jacobian comparison; normal crossings; pole order; and RLCT.
