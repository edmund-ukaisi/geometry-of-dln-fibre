# Review: A2 selected-entry chart-point measure bridge

## Source-scope scout

Reviewer: `Euler the 4th`, xhigh read-only source-scope review.

Status: PASS.

Findings:

- The checkpoint is faithful if narrowly scoped to the finite selected-entry
  coordinate bridge from center-indexed signed-box coordinates to the
  normal-crossing microcertificate chart point.
- The pen-and-paper calculation to reproduce is the substitution
  `x_p = u`, `x_i = u r_i`, the loss factorization
  `sum x_i^2 = u^2 * (1 + sum r_i^2)`, and the triangular derivative
  determinant `u^(|E|-1)`.
- The pivot hyperplane must be handled as a measure-zero locus; injectivity is
  only on `u != 0`.
- Full `SelectedEntryAnalyticJacobianVolumeData` should be deferred.

## Lean/API scout

Reviewer: `Halley the 4th`, xhigh read-only Lean/API review.

Status: PASS.

Findings:

- Recommended a new small module importing both `SelectedEntryNormalCrossing`
  and `SelectedEntrySignedBoxMeasure`, keeping measure imports out of the
  finite normal-crossing file.
- Recommended exposing the adapter
  `y |-> sourceChartPoint pivot (y pivot) (CenterCoord.sourceResidual y)`,
  proving the chart-map equality, and then optionally transporting the
  signed-box pushforward.
- Identified useful existing APIs:
  `CenterCoord.chartMap`, `CenterCoord.sourceDensity`,
  `map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image`,
  `selectedEntryCenterSqFormalJacobianChartCertificate.sourceChartPoint`, and
  `chartMap_sourceChartPoint_eq`.
- Warned not to attempt direct `SelectedEntryAnalyticJacobianVolumeData`.

## Implementation review

Reviewer: `Ptolemy the 4th`, xhigh read-only implementation review.

Status: PASS.

Findings:

- The Lean scope is faithful to the reproduction and source boundary.  The
  module states only a finite coordinate-presentation bridge, exposes the
  chart-point adapter, proves the composite equality, and restates the existing
  signed-box pushforward.
- No theorem name, docstring, or statement-card claim overstates analytic atlas
  construction, source-prior transport, Haar/Jacobian transport, coverage,
  normal crossings, pole order, or RLCT.  The phrase `jacobianPrior` is
  acceptable because it names the existing finite certificate field.
- The two-stage measure theorem legitimately uses measurable `Measure.map_map`:
  the file proves measurability of `chartPointAdapter` and `formalChartMap`
  from continuity before rewriting the two maps.
- Process notes addressed after review: the new `DLNFibre.lean` import was
  moved to the physical end, and this implementation review section was
  updated from pending to PASS.

## Verification

Focused build of
`DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge` and full
`DLNFibre` build passed via `scripts/lb`; only pre-existing replay warnings
appeared.  `scripts/sorries`, `git diff --check`, and the touched Lean-file
forbidden-marker scan passed.  Direct axiom probes for
`formalChartMap_chartPointAdapter_eq_chartMap` and
`map_formalChartMap_map_chartPointAdapter_weightedSignedBox_eq_restrict_image`
reported `[propext, Classical.choice, Quot.sound]`.
