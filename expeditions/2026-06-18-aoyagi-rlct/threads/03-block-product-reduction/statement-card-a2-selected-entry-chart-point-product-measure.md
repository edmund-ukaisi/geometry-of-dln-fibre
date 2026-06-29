# Statement card: A2 selected-entry chart-point product measure

> **Claim.** For a fixed selected-entry pivot, the chart-point adapter sends
> the center signed-box product measure exactly to the natural product of the
> pivot interval measure and the erased-center residual interval product
> measure.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge`.
> - **Gloss.** The adapter is the finite coordinate split
>   `y |-> (y_p, y|_{center.erase p})`.  Product measure on the center-indexed
>   signed box therefore splits as the product of the pivot interval measure
>   and the residual product measure.
> - **Proved.** `erasePivotEquivCompl`, `chartPointProductMeasure`,
>   `chartPointSplitEquiv`, its coordinate formulas, equality with
>   `chartPointAdapter`, `measurePreserving_chartPointSplitEquiv_signedBoxMeasure`,
>   and `map_chartPointAdapter_signedBoxMeasure_eq_chartPointProductMeasure`.
> - **Assumed.** A finite center and a selected pivot.  No positivity
>   hypothesis on radii is needed for the measure equality.
> - **Cited.** None.  This is finite product-measure bookkeeping using
>   Mathlib's product-measure equivalence API.
> - **Deferred.** Any use of this product measure as a field in a supplied
>   analytic atlas constructor; source-domain coverage; transition regularity;
>   source production; branch termination; original/source-prior domination.
> - **Nonclaims.** No analytic atlas construction, no source-prior transport,
>   no determinant-chart Haar theorem, no source-image or source-rank coverage,
>   no normal-crossing extraction, no pole order, and no RLCT.
> - **Status.** Lean implemented; focused build passed.  Source-scope,
>   Lean/API, and implementation reviews gave PASS.
