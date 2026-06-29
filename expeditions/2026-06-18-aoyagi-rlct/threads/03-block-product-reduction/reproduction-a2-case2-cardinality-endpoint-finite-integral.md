# Reproduction - A2 Case 2 cardinality endpoint finite integral

Date: 2026-06-29.

Status: reproduced; Lean target selected.

## Target

The strongest chart-produced Case 2 local-measure theorem currently assumes
endpoint equivalences

```text
eNext : tau ~= Case2ResidualColIndex n S (J + 1),
e q   : case2PostPivotTwoEdgeDomain n S J tau q
          ~= throughSubspaceEndpointComplementIndex ... q.
```

These equivalences are not canonical data from Aoyagi's calculation; they are
finite reindexings.  The next handoff should allow callers to supply finite
cardinality equalities instead:

```text
card tau = card (Case2ResidualColIndex n S (J + 1)),

card (case2PostPivotTwoEdgeDomain n S J tau q)
  = card (throughSubspaceEndpointComplementIndex ... q).
```

From these equalities Lean already constructs noncanonical equivalences by
`case2EndpointTransportEquivs_of_card_eq`.  The intended theorem is therefore a
cardinality-entry wrapper for

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density.
```

## Calculation

Let

```text
center = case2ResidualBlockPivotEntries n S (J + 1),
pivotNext = (J + 2, J + 2) in center.
```

Given `hNext` and `hEndpoints`, define

```text
equivs =
  case2EndpointTransportEquivs_of_card_eq
    (kappa := throughSubspaceEndpointComplementIndex ...)
    n S J hNext hEndpoints,
eNext = equivs.1,
e = equivs.2.
```

Then set

```text
retainedData yNext =
  (case2PostPivotSelectedEntryRetainedPassiveData
    n hS hcont hnext yNext eNext).endpointTransport e,

sourceChart yNext =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (retainedData yNext).
```

The existing radius theorem applies verbatim to these constructed equivalences.
All analytic and measure hypotheses remain exactly the same:

- fixed-base source data for the identity edge-family source chart;
- add-Haar measure on regular coordinates;
- positive residual signed-box radii;
- the selected-entry critical inequality;
- positive continuous local density at `(base,0)`;
- the local loss lower bound on the retained-passive p.13 local source.

The proof performs no new algebra after the equivalence construction.  It is a
bookkeeping move from supplied equivalence data to finite-cardinality data.

## Boundary Checks

- The equivalences are noncanonical `Fintype.equivOfCardEq` equivalences.
  Labels are not preserved.
- The theorem does not prove the cardinality equalities.  It only consumes
  them.
- The theorem does not identify an original DLN source prior or compare an
  external Jacobian density.
- The source measure remains the selected-entry signed-box measure pushed
  forward through the constructed retained-passive p.13 source chart.
- No normal crossings, pole order, or RLCT extraction is proved.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** Finite endpoint-cardinality equalities are
sufficient to instantiate the endpoint-transported Case 2 chart-produced
finite-integral handoff with positive continuous density, using the existing
noncanonical endpoint-equivalence constructor.

**Assumed.** The fixed-base two-edge context, finite-dimensional endpoints,
`hS`, `hcont`, `hnext`, the two endpoint-cardinality hypotheses, source data,
positive radii and density, critical inequality, and the local loss lower
bound.

**Cited.** None.

**Deferred.** Proof/provenance of the endpoint cardinalities in a particular
source-data situation; label-preserving equivalences; original source-prior
transport; Jacobian comparison for an external prior; normal crossings; pole
order; and RLCT.
