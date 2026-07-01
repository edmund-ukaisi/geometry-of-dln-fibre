# Reproduction - A2 Case 2 product source chart p.13 source-set support

Date: 2026-07-01.

Status: pen-and-paper check for the local support version of the concrete p.13
product-coordinate source chart.

## Question

The existing product-chart support theorem lands in the retained-passive local
source:

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource
  W2 B2 U0 hU0 (fun E : EdgeFamily => E).
```

Can the same small-ball support be stated in the named p.13 source edge-family
set?

## Calculation

The local source is definitionally the preimage of the named p.13 source set
under the supplied edge-family map:

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet
```

In the concrete product-source theorem the map is the identity on

```text
EdgeFamily =
  forall p : Fin 2,
    reverseVertex W2 p.castSucc ->L[R] reverseVertex W2 p.succ.
```

Therefore membership in the retained-passive local source is exactly
membership in

```text
paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet W2 B2 U0 hU0.
```

The existing small-ball theorem already supplies `R > 0`, `R <= Rmax`, and
eventual membership of

```text
productSourceChart(theta, u)
```

in the local source for all `u in ball 0 R`.  Rewriting the local-source
membership along the preimage identity gives the named-source-set version.
The same rewrite applies to the measure support theorem: if the pushed-forward
small-ball product measure is supported on the local source, then it is
supported on the equal named source set.

## Boundary

This is support bookkeeping.  It does not prove that the product source chart
has a full inverse, that its image covers a source neighborhood, or that the
original edge-family prior has the required density on that image.

## Lean Target

Add to
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean`:

```text
exists_pos_radius_le_case2PassiveThetaEndpointProductSourceChart_mem_p13SourceEdgeFamilySet_nhdsWithin_source

exists_pos_radius_open_measure_map_case2PassiveThetaEndpointProductSourceChart_restrict_sourceRankStratum_ball_p13SourceEdgeFamilySet_eq_self
```

Both proofs should wrap the existing retained-passive local-source theorems and
rewrite by
`paperEndpointFixedBaseRetainedPassiveP13LocalSource_eq_preimage_sourceEdgeFamilySet`.

## Nonclaims

No full product-chart readback, no source-image equality, no source-rank
coverage, no original/source-prior density comparison, no Haar transport, no
normal crossings, no pole order, and no RLCT extraction.
