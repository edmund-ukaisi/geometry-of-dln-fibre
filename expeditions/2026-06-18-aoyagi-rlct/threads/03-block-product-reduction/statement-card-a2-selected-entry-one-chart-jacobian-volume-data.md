# Statement card: A2 selected-entry one-chart Jacobian/volume data

> **Claim.** For a fixed selected-entry pivot and positive signed-box radii,
> the finite chart-point volume-form pushforward supplies one
> `SelectedEntryAnalyticJacobianVolumeData` record for the single
> selected-entry chart with `sourceDomain = univ`, `chartDomain = univ`, and
> target `chartMap pivot '' signedBoxSet R`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge` and
>   `DLNFibre.DLN.Aoyagi.SelectedEntryOneChartJacobianVolumeData`.
> - **Gloss.** In chart-point coordinates `(u, r)`, the map is
>   `(u, r) |-> (x_p = u, x_i = u r_i)`, and the absolute Jacobian density is
>   `|u|^(# center.erase pivot.1)`.
> - **Proved.**
>   `map_formalChartMap_chartPointProductMeasure_withDensity_eq_restrict_image`,
>   `selectedEntryOneChartAnalyticAtlasContext`, and
>   `selectedEntryOneChartAnalyticJacobianVolumeData`.
> - **Assumed.** A finite center, a selected pivot, and positive radii
>   `forall i, 0 < R i` for the data record's target-nonempty and nonzero
>   restricted-source fields.  The pushforward equality itself has no
>   positivity hypothesis.
> - **Cited.** None.  This is finite selected-entry measure bookkeeping using
>   the already-formalized Jacobian pushforward and chart-point product
>   measure bridge.
> - **Deferred.** Source-domain coverage, chart and transition regularity for
>   a full atlas, unit regularity as analytic data, source production, branch
>   termination, original/source-prior transport, and all normal-crossing
>   extraction consequences.
> - **Nonclaims.** No full analytic atlas producer, no source coverage, no
>   source-prior theorem, no determinant-chart Haar theorem, no source-rank
>   coverage, no normal-crossing extraction, no pole order, and no RLCT.
> - **Status.** Lean implemented; focused/full builds, hygiene checks, axiom
>   probes, and xhigh implementation review passed.
