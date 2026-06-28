# Statement card - A2 Case 2 inverse-Jacobian residual-source handoff

## Claim

For the two-edge Case 2 endpoint-transported selected-entry chart, the
determinant-chart selected-entry residual theorem supplies the chart-side
residual positivity and finite residual negative-power integral inputs needed
by the raw-order retained-passive inverse-Jacobian source-measure sockets.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Declarations:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.
  residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map

PaperEndpointFixedBaseRegularCoordinateSourceData.
  exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_case2EndpointTransport_selectedEntrySignedBox_map
```

## Statement

Let

```text
chart y =
  topologyTuple
    ((case2PostPivotSelectedEntryRetainedPassiveData
      n hS hcont hnext y eNext).endpointTransport e)
```

and let

```text
mu =
  Measure.map rawChart
    ((m.restrict topologyTupleRawOrderSourceRecursiveDetChartSet)
      .withDensity inverseJacobianDensity).
```

Assume the determinant-chart pushforward identity for `chart`, target
positive-set measurability for the direct retained-passive residual, positive
signed-box radii, `0 <= t`, and the selected-entry exponent inequality

```text
2 * t < ((center.erase pivotNext.1).card : R) + 1.
```

Then the raw-order inverse-Jacobian source measure satisfies the p.13
residual-source hypotheses over the identity retained-passive local source:
the residual is positive `mu.restrict localSource`-a.e. and its negative
`t`-power is integrable there.

The finite-integral declaration additionally assumes `sourceData`, `[SFinite
m]`, a regular-coordinate Haar measure `nu`, `loss`, `density`, `0 < R`,
`0 < c`, `0 <= C`, `0 < t`, and the local loss lower bound plus density
nonnegativity and upper-bound hypotheses.  It concludes the corresponding
open-neighborhood finite lower-integral statement for the p.13 regular
coordinates and raw-order inverse-Jacobian source measure.

## Source / Proof Basis

Aoyagi PDF pp. 11-13 for the retained-passive p.13 determinant/source chart
and pp. 19-22 for the Case 2 selected-entry chart.  The proof uses only the
already-formalised selected-entry determinant-chart residual handoff and the
raw-order inverse-Jacobian source-measure sockets:

```text
retainedPassiveP13Canonical_detChart_residual_pos_ae_and_lintegral_rpow_neg_of_case2EndpointTransport_selectedEntrySignedBox_map
residualSourceHypotheses_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13RawOrderSourceChart_withDensity_inverseJacobian_of_chartSide
```

## Boundary

This discharges the chart-side residual hypotheses for the raw-order
inverse-Jacobian sockets in the Case 2 endpoint-transported selected-entry
lane.  It does not prove the determinant-chart pushforward identity, target
positive-set measurability, chart coverage, original external source-prior
transport, local loss or density bounds, source-rank coverage, normal
crossings, pole order, or RLCT extraction.

## Verification Plan

Run focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`,
then `scripts/sorries`, `git diff --check`, touched-file forbidden-marker
search, direct dependency probes, and xhigh review.

## Verification Result

Focused build of `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure`
passed via the worktree-local `scripts/lb` command.  `scripts/sorries`,
`git diff --check`, touched-file forbidden-marker search, and direct dependency
probes passed; both new declarations report only
`[propext, Classical.choice, Quot.sound]`.  Xhigh read-only review by Godel
passed.
