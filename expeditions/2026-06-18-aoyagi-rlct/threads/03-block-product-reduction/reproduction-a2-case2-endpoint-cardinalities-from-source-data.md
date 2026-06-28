# Reproduction - A2 Case 2 endpoint cardinalities from source data

## Source Shape

Aoyagi's Case 2 two-edge post-pivot family has three endpoint types:

```text
q = 0: tau,
q = 1: Case2ResidualColIndex n S (J+1),
q = 2: Case2ResidualRowIndex n S (J+1).
```

The fixed-base p.13 source-data endpoint family is

```text
throughSubspaceEndpointComplementIndex
  (reverseVertex W2) (reverseEdge W2 B2) U0 q.
```

The previous endpoint-cardinality rung proved that source data computes its
endpoint cardinality as

```text
card endpoint(q) = H(q.rev.val + 1) - r.
```

For a two-edge chain, the reverse index values are:

```text
(0 : Fin 3).rev.val = 2,
(1 : Fin 3).rev.val = 1,
(Fin.last 2).rev.val = 0.
```

Therefore the fixed-base endpoint cardinalities are `H 3 - r`, `H 2 - r`,
and `H 1 - r`.

## Derivation

Assume the displayed endpoint-size identifications:

```text
hTau : card tau = H 3 - r,
hCol : card (Case2ResidualColIndex n S (J+1)) = H 2 - r,
hRow : card (Case2ResidualRowIndex n S (J+1)) = H 1 - r.
```

For `q = 0`, unfolding `case2PostPivotTwoEdgeDomain` gives
`case2PostPivotTwoEdgeDomain n S J tau 0 = tau`, so

```text
card (case2PostPivotTwoEdgeDomain n S J tau 0)
  = card tau
  = H 3 - r
  = card endpoint(0).
```

For `q = 1`, the domain is `Case2ResidualColIndex n S (J+1)`, so

```text
card (case2PostPivotTwoEdgeDomain n S J tau 1)
  = card (Case2ResidualColIndex n S (J+1))
  = H 2 - r
  = card endpoint(1).
```

For `q = 2`, the domain is `Case2ResidualRowIndex n S (J+1)`, so

```text
card (case2PostPivotTwoEdgeDomain n S J tau 2)
  = card (Case2ResidualRowIndex n S (J+1))
  = H 1 - r
  = card endpoint(2).
```

Since `Fin 3` has only these three cases, this proves the endpoint-family
cardinality hypothesis consumed by `case2EndpointTransportEquivs_of_card_eq`.

## Boundary

This derivation only removes the pointwise endpoint-cardinality family
`hEndpoints` once the three scalar size equalities are known.  It does not
prove `hTau`, `hCol`, or `hRow`; in particular, `tau` is still an arbitrary
endpoint type and its geometric origin is not constructed here.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** The pointwise endpoint-cardinality equality
for the Case 2 two-edge endpoint family from fixed-base source data and three
explicit endpoint-size equalities.

**Assumed.** Fixed-base source data; the scalar equalities `hTau`, `hCol`, and
`hRow`.

**Reused/cited.**
`PaperEndpointFixedBaseRegularCoordinateSourceData.endpointComplementIndex_card_eq_H_rev_sub_rank`.
There is no new analytic or RLCT citation.

**Deferred.** Construction of `tau`; proof of residual row/column cardinality
from a source-rank or Definition 3 package; canonical or label-preserving
endpoint equivalences; selected-entry preservation; source-prior transport;
Jacobian comparison; normal crossings; pole order; RLCT.
