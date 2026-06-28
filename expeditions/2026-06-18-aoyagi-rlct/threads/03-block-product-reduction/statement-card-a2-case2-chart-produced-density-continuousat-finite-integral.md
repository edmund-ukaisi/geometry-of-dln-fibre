# Statement Card - A2 Case 2 chart-produced density continuous-at finite integral

## Claim

For the endpoint-transported explicit Case 2 selected-entry chart-produced
measure, local finite integrability follows from a positive continuous density
at `(base,0)`, after shrinking the regular-coordinate radius.  This replaces
the explicit eventual nonnegativity and boundedness hypotheses for the density.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the p.13 retained-passive local source and pp. 19-22
for the Case 2 selected-entry chart.  The proof is finite/topological measure
handoff, not a new analytic extraction theorem.  Lean dependencies:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
Metric.ball_subset_ball
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Expected declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_chartProducedMeasure_continuousAt_pos_density
```

## Nonclaims

No construction of endpoint equivalences, no label-preserving endpoint
provenance, no source-rank coverage, no original prior or external source
measure identification, no Jacobian comparison for such a prior, no normal
crossings, no pole order, and no RLCT.

Retained Lean hypotheses include the finite-dimensional fixed-base endpoint
context, `hS`, `hcont`, `hnext`, `U₀`, `hU₀`, the `EdgeFamily` measurable /
open-measurable / Borel instances, `0 < creg`, `0 < t`, positive residual
radii, the Case 2 critical inequality, `ν.IsAddHaarMeasure`, and the local
loss lower bound on the larger radius `Rmax`.

## Verification Plan

Run focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`, then
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker search,
direct axiom probe for the new declaration, and xhigh review.
