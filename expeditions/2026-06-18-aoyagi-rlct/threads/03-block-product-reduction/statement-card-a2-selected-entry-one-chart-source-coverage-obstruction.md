# Statement card: A2 selected-entry one-chart source-coverage obstruction

> **Claim.** If the finite center has a non-pivot coordinate `q`, then the
> exact one-chart selected-entry context with `sourceDomain = univ` has no
> `SelectedEntryAnalyticSourceCoverageData`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.SelectedEntryOneChartSourceCoverageObstruction`.
> - **Gloss.** The selected-entry chart has form
>   `(u, r) |-> (x_p = u, x_i = u r_i)`.  If the pivot output is zero, then
>   the whole output is zero.  The vector with pivot coordinate `0` and
>   non-pivot coordinate `1` lies in `univ` but not in the single chart image.
> - **Proved.**
>   `formalChartMap_pivot`,
>   `formalChartMap_eq_zero_of_fst_eq_zero`, and
>   `not_selectedEntryOneChartAnalyticSourceCoverageData_of_ne`.
> - **Assumed.** A finite center, selected pivot, and an explicit non-pivot
>   coordinate `q` with `q != pivot`.
> - **Cited.** None.
> - **Deferred.** Source coverage for smaller domains, source coverage by a
>   multi-pivot atlas, and all supplied analytic-atlas producer fields.
> - **Nonclaims.** No obstruction to a different source domain, no obstruction
>   to a multi-pivot atlas, no source production, no branch termination, no
>   source-prior theorem, no determinant-chart Haar theorem, no source-rank
>   coverage, no normal-crossing extraction, no pole order, and no RLCT.
> - **Status.** Pen-and-paper reproduction complete; focused Lean build passed;
>   xhigh source/scope and Lean/API reviews passed.
