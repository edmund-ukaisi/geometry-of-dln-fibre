# Statement card: A2 selected-entry chart-target nonzero measure

> **Claim.** For one selected-entry signed-box chart with positive radii, the
> chart image has nonzero Lebesgue measure; the corresponding restricted
> target measure and weighted signed-box source measures are nonzero.  The
> chart-point bridge inherits the same nonzero statement for the adapter and
> two-stage chart-point pushforward.
>
> - **Lean:** target modules
>   `DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure` and
>   `DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge`.
> - **Gloss.** Inside the target image of
>   `SelectedEntrySignedBox.CenterCoord.chartMap pivot`, use the concrete box
>   `R_p/2 < x_p < R_p` and
>   `|x_i| < R_p R_i / 4` for `i != p`.  The quotient coordinates then satisfy
>   `|x_i/x_p| < R_i`, so the existing horn criterion puts the box inside the
>   selected-entry chart image.  Since the box is nonempty open, the image has
>   positive Lebesgue measure.
> - **Proved.** `chartMapTargetInnerBox`, openness/nonemptiness of the inner
>   box, its inclusion in the chart image, nonzero Lebesgue measure of the
>   chart image, nonzero restricted Lebesgue target measure, nonzero
>   punctured-source image target measure, nonzero full and punctured weighted
>   source measures, and chart-point adapter/two-stage nonzero corollaries.
> - **Assumed.** A finite center, a selected pivot, and strictly positive
>   signed-box radii `forall i, 0 < R i`.
> - **Cited.** None.  The selected-entry substitution is the elementary
>   Aoyagi blow-up chart in the product-reduction proof (PDF pp. 15-22); the
>   Jacobian pushforward theorem reused here was already proved in
>   `SelectedEntrySignedBoxMeasure.lean`.
> - **Deferred.** Natural chart-point product measure transport; a
>   constructor for `SelectedEntryAnalyticJacobianVolumeData`; source-domain
>   coverage; transition regularity; source production; branch termination;
>   original/source-prior local domination.
> - **Nonclaims.** No analytic atlas construction, no source-prior transport,
>   no determinant-chart Haar theorem, no raw/source Haar theorem, no
>   source-image or source-rank coverage, no normal-crossing extraction, no
>   pole order, and no RLCT.
> - **Status.** Lean implemented; focused builds, full `DLNFibre` build,
>   `scripts/sorries`, `git diff --check`, touched Lean-file marker scan, and
>   direct axiom probes passed.  Xhigh source-scope, Lean/API, and
>   implementation reviews gave PASS.
