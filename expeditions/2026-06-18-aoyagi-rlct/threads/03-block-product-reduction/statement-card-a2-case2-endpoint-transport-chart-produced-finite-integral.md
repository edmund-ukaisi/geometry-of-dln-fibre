# Statement card - A2 Case 2 endpoint-transport chart-produced finite integral

## Claim

The endpoint-transported explicit Case 2 fixed-base source chart is continuous,
and its selected-entry signed-box pushforward measure satisfies the
retained-passive local finite-integral handoff under explicit loss, density,
radii, exponent, source-data, and measurable-space hypotheses.

## Lean Targets

Files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Target names:

```lean
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport
ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_endpointTransport_detChart_subtype
PaperEndpointFixedBaseRegularCoordinateSourceData.continuous_retainedPassiveP13SourceEdgeFamilyOfData_of_case2EndpointTransport
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
```

## Proof Basis

Endpoint transport is finite product-coordinate submatrix reindexing, hence
continuous.  The Case 2 source chart is the composition of the continuous
selected-entry retained-passive datum, continuous endpoint transport, and the
continuous fixed-base retained-passive source-chart map.  The finite-integral
theorem applies the generic chart-produced selected-entry handoff using the
Case 2 local-source membership and source-readback matrix identity.

## Nonclaims

This checkpoint does not construct endpoint equivalences, identify an original
source prior, compare Jacobians for an external prior, prove source-rank
coverage, prove normal crossings, compute pole order, or extract RLCT.

## Status

Focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure` passed with only
the existing imported warning profile.  `scripts/sorries`, `git diff --check`,
touched-Lean-file forbidden-marker search, and direct axiom-footprint probes
passed; the four public theorem names depend only on `[propext,
Classical.choice, Quot.sound]`.  Reviewed PASS by xhigh `Hubble` in
`review-a2-case2-endpoint-transport-chart-produced-finite-integral.md`.
