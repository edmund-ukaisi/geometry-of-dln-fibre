# Reproduction - A2 with-following rank-cut original-prior local loss source data from rank equations

Date: 2026-07-07.

Status: Lean wrapper proved locally.

## Claim

The strongest current rank-cut original-prior local-loss wrapper with
`Module.finBasis` endpoint bases and regular-coordinate `volume` still asks the
caller to supply

```text
PaperEndpointFixedBaseRegularCoordinateSourceData
  W2 B2 U0 hU0 (sourceChart z0) (fun E => E) H r rEdge.
```

For the Case 2 with-following p.13 source chart, this source-side package can
be built from explicit local data:

```text
forall k : Fin 3, H(k.val + 1) = finrank(W2 k),
r + rank(z0.2) = rEdge 0,
r + rank(successorSelectedEntryMatrix(z0)) = rEdge 1,
sourceChart z0 = reverseEdge(W2,B2).
```

This removes only the opaque `sourceData` argument from the returned
continuation.  It does not remove the residual zero-locus nullity hypothesis,
the fixed-base centering equality, the product-zero density hypotheses, or the
raw Haar input.

## Source-Side Construction

The source data constructor is purely source-side.  It takes the source edge
family map

```text
Cedge : EdgeFamily -> EdgeFamily
Cedge E = E
```

at the base point `sourceChart z0`.  Its continuity input is therefore
`continuousAt_id`, not continuity of the theta-side source chart.

The base equality input is exactly

```text
sourceChart z0 = fun p => reverseEdge(W2,B2,p).
```

This remains a hypothesis.  The wrapper does not prove that an arbitrary
theta-side base point is centered at the fixed paper base.

The source-stratum membership input is obtained pointwise from the Case 2
source-image rank theorem:

```text
case2PassiveThetaWithFollowingFactorEndpointSourceChart_mem_sourceRankStratum.
```

The determinant-chart hypothesis for this theorem comes from

```text
case2PassiveThetaWithFollowingFactorEndpointRetainedData_detChart
```

applied to `hGdet hz0G`.  The rank equations supplied by the caller identify
the active following factor rank and the successor selected-entry matrix rank
with `rEdge 0` and `rEdge 1` after adding the base-product rank `r`.

Finally,

```text
paperEndpointFixedBaseRegularCoordinateSourceData_of_local_source_basepoint
```

combines `continuousAt_id`, the fixed-base centering equality, the
source-stratum membership, and the dimension convention `hH`.

## Nonclaims

- No proof of residual zero-locus nullity.
- No proof that `sourceChart z0` is the fixed reverse-edge base family.
- No proof of the two rank equations.
- No source-rank coverage or converse chart-image theorem.
- No source-prior or original-prior transport.
- No determinant/raw Haar transport.
- No product-zero density continuity or positivity proof.
- No normal-crossing construction, pole-order count, or RLCT extraction.

## Review

Xhigh scout `Beauvoir` checked the pen-and-paper boundary: this is a
source-side p.13 coordinate certificate, not an analytic regular-suspension or
RLCT theorem.  Xhigh scout `Russell` checked the Lean route and specifically
warned that the continuity needed for the constructed `sourceData` is
`continuousAt_id` on the source edge-family space.  Xhigh scout `Huygens`
audited the theorem boundary and found no hidden canonical-basis,
prior-coordinate, zero-locus, source-base, normal-crossing, or RLCT claim.
