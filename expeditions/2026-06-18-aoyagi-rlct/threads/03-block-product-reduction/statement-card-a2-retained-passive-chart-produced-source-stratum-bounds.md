# Statement Card - A2 retained-passive chart-produced source-stratum bounds

Date: 2026-06-29.

## Claim

The retained-passive selected-entry finite-integral handoff can be stated for
the chart-produced selected-entry signed-box source measure while taking the
loss and density bounds on the source-rank stratum.

## Lean Targets

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean
```

Generic chart-produced declaration:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
```

Retained-data declaration:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure
```

Continuous-density retained-data declaration:

```text
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_of_sourceEdgeFamilyOfData_chartProducedMeasure_continuousAt_pos_density
```

Case 2 declarations:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure
exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_sourceEdgeFamilyOfData_selectedEntryCenter_signedBox_withDensity_sourceStratum_bounds_chartProducedMeasure_continuousAt_pos_density
```

## Inputs Kept Explicit

- chart support in the retained-passive p.13 local source;
- selected-entry residual readout;
- positive selected-entry radii and critical inequality;
- source-stratum loss lower bound;
- source-stratum density nonnegativity and upper bound, or density continuity
  and positivity in the continuous-density variant.

## Nonclaims

The result is still only for the selected-entry chart-produced source measure.
It proves no selected-entry chart image equality, no source-rank coverage, no
external/original source-prior transport, no Jacobian comparison, no analytic
atlas, no normal crossings, no pole order, and no RLCT statement.

## Verification

Focused Lean builds passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
```

The full `DLNFibre` build also passed.  `lean/scripts/sorries` reported no
forbidden declarations or exits, `git diff --check` passed, and the touched
Lean-file forbidden-marker scan was clean.

Independent xhigh review passed in
`review-a2-retained-passive-chart-produced-source-stratum-bounds.md`.
