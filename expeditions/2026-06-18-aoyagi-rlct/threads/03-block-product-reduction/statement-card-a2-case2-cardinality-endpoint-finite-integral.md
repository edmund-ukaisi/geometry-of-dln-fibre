# Statement Card - A2 Case 2 cardinality endpoint finite integral

## Claim

The endpoint-transported Case 2 chart-produced finite-integral theorem can be
stated with finite endpoint-cardinality equalities instead of supplied endpoint
equivalences.  The equivalences used internally are the noncanonical finite
equivalences from `case2EndpointTransportEquivs_of_card_eq`.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the retained-passive p.13 source chart and pp. 19-22
for the Case 2 selected-entry chart.  This theorem is finite reindexing plus
the already-proved local-measure handoff.  Lean dependencies:

```text
case2EndpointTransportEquivs_of_card_eq
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Expected declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density_card_eq
```

## Nonclaims

No construction of the cardinality equalities, no label-preserving endpoint
transport, no source-rank coverage, no original prior or external source
measure identification, no Jacobian comparison for such a prior, no normal
crossings, no pole order, and no RLCT.

Retained Lean hypotheses include the finite-dimensional fixed-base endpoint
context, `hS`, `hcont`, `hnext`, `U₀`, `hU₀`, the endpoint-cardinality
equalities, `EdgeFamily` measurable/open-measurable/Borel instances,
`ν.IsAddHaarMeasure`, source data, `0 < Rmax`, `0 < creg`, `0 < t`, positive
residual radii, the Case 2 critical inequality, positive continuous density at
`(base,0)`, and the local loss lower bound.

## Verification Plan

Run focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`, then
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker search,
direct axiom probe for the new declaration, and xhigh review.
