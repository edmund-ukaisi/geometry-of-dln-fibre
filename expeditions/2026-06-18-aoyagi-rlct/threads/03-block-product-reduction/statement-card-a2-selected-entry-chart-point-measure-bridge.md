# Statement card: A2 selected-entry chart-point measure bridge

> **Claim.** The center-indexed selected-entry signed-box chart factors through
> the one-chart normal-crossing microcertificate chart point, and the existing
> signed-box weighted pushforward theorem has an equivalent one-stage and
> two-stage chart-point presentation.
>
> - **Lean:** target module
>   `DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge`, in
>   `lean/DLNFibre/DLN/Aoyagi/SelectedEntryChartPointMeasureBridge.lean`.
> - **Gloss.** For a finite center and pivot, define
>   `chartPointAdapter pivot y = (y pivot, y|_{center.erase pivot})` and
>   expose the certificate chart map as `formalChartMap pivot`.  Then
>   `formalChartMap pivot (chartPointAdapter pivot y) =
>   SelectedEntrySignedBox.CenterCoord.chartMap pivot y`.  The adapter also
>   identifies the certificate coordinate, loss unit, and absolute
>   Jacobian/prior factor with the center-coordinate pivot, residual unit, and
>   `sourceDensity`.
> - **Proved.** `FormalChartPoint`, `chartPointAdapter`,
>   `formalChartMap`, visible residual extension, continuity and measurability
>   of both maps, pointwise chart-map equality, coordinate/loss-unit/density
>   compatibility, one-stage chart-point signed-box pushforward, and two-stage
>   pushforward through `Measure.map (chartPointAdapter pivot)`.
> - **Assumed.** Only the finite selected-entry setup: `DecidableEq` on the
>   ambient index type, a finite center, a chosen pivot, and signed-box radii
>   for the inherited signed-box theorem.  No source-prior or analytic atlas
>   hypotheses are introduced.
> - **Cited.** None.  The underlying selected-entry substitution is the
>   elementary Aoyagi blow-up chart in the product-reduction proof (PDF
>   pp. 15-22); the measure theorem reused here was already proved in
>   `SelectedEntrySignedBoxMeasure.lean`.
> - **Deferred.** Direct construction of
>   `SelectedEntryAnalyticJacobianVolumeData`; chart domains and targets in
>   the analytic producer shape; nonzero restricted source measure; original
>   source-prior transport; source coverage; transition regularity; source
>   production; branch termination.
> - **Nonclaims.** No determinant-chart Haar theorem, no raw/source Haar
>   theorem, no external/original source-prior comparison, no retained-passive
>   passive-variable Jacobian, no source-rank/source-image coverage, no
>   analytic chart-domain coverage, no normal-crossing extraction theorem, no
>   pole order, and no RLCT.
> - **Status.** Lean implemented; focused build, full `DLNFibre` build,
>   `scripts/sorries`, `git diff --check`, touched Lean-file marker scan, and
>   direct axiom probe passed; xhigh source-scope, Lean/API, and
>   implementation reviews gave PASS.
