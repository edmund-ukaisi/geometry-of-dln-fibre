# Statement card: A2 selected-entry chart-point weighted product measure

> **Claim.** For a fixed selected-entry pivot, the chart-point adapter sends
> the center signed-box product measure weighted by `sourceDensity` to the
> chart-point product measure weighted by the pivot-coordinate density
> `|x.1|^(# center.erase pivot.1)`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge`.
> - **Gloss.** The adapter is `y |-> (y_p, y|_{center.erase p})`, so the
>   selected-entry density `|y_p|^(# center.erase p)` pulls forward to the
>   chart-point density depending only on the first coordinate.
> - **Proved.** `chartPointDensity`,
>   `chartPointDensity_chartPointAdapter_eq_sourceDensity`,
>   `aemeasurable_chartPointDensity`, and
>   `map_chartPointAdapter_withDensity_sourceDensity_eq_chartPointProductMeasure_withDensity`.
> - **Assumed.** A finite center and a selected pivot.  No positivity
>   hypothesis on radii is needed for this measure equality.
> - **Cited.** None.  This is finite product-measure and `withDensity`
>   bookkeeping using the selected-entry density formula already formalized in
>   Lean.
> - **Deferred.** Any use of this weighted chart-point measure as part of
>   `SelectedEntryAnalyticJacobianVolumeData`; source-domain coverage;
>   transition regularity; source production; branch termination;
>   original/source-prior domination.
> - **Nonclaims.** No analytic atlas construction, no source-prior transport,
>   no determinant-chart Haar theorem, no source-image or source-rank
>   coverage, no normal-crossing extraction, no pole order, and no RLCT.
> - **Status.** Lean implemented; focused build passed.  Source-scope,
>   Lean/API, and implementation reviews gave PASS.
