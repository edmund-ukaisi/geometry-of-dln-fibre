# Statement Card - A2 retained-passive source-edge-family density continuous-at finite integral

## Claim

For the generic retained-passive source-edge-family chart-produced measure,
local finite integrability follows from a positive continuous density at
`(base,0)`, after shrinking the regular-coordinate radius.  This replaces the
explicit eventual density nonnegativity and boundedness hypotheses of the
generic source-edge-family handoff.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the retained-passive p.13 source-coordinate
construction and pp. 19-22 for the selected-entry chart shape.  The proof is a
finite/topological density-bound handoff, not normal-crossing extraction.
Lean dependencies:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure
exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
Metric.ball_subset_ball
```

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Expected declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density
```

## Nonclaims

No endpoint-equivalence construction, no label-preserving endpoint provenance,
no original prior or external source measure identification, no Jacobian
comparison for such a prior, no source-rank coverage, no normal crossings, no
pole order, and no RLCT.

Retained hypotheses include the finite-dimensional fixed-base context,
ambient `EdgeFamily` measurable/open-measurable/Borel instances,
determinant-subtype measurable/open-measurable instances, `hdet`,
`residualCoordEquiv`, `hdataFactor`, `hretainedData`, source data for
`Cedge := fun E : EdgeFamily => E`, `0 < Rmax`, `0 < creg`, `0 < t`,
positive residual radii, the selected-entry critical inequality,
`nu.IsAddHaarMeasure`, and the local loss lower bound on `ball 0 Rmax`.

## Verification Plan

Run focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure`, then
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker search,
direct axiom probe for the new declaration, and xhigh review.
