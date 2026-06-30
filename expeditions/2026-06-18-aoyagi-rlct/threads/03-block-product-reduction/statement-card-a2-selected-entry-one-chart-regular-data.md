# Statement card: A2 selected-entry one-chart regular data

> **Claim.** For a fixed selected-entry pivot, the same one-chart context used
> for the selected-entry Jacobian/volume record carries chart regularity,
> identity transition regularity, and unit regularity data on universal source
> and chart domains.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.SelectedEntryOneChartRegularData`.
> - **Gloss.** The chart map `(u, r) |-> (x_p = u, x_i = u r_i)` is
>   continuous componentwise, the unique normal-crossing coordinate is `u`,
>   the only one-chart transition is the identity, the loss unit is
>   `1 + sum r_i^2`, and the Jacobian/prior unit is constant `1`.
> - **Proved.**
>   `continuous_chartPointCoord`, `continuous_chartPointLossUnit`,
>   `continuous_chartPointJacobianPriorUnit`,
>   `selectedEntryOneChartAnalyticChartRegularData`,
>   `selectedEntryOneChartAnalyticTransitionRegularData`, and
>   `selectedEntryOneChartAnalyticUnitRegularData`.
> - **Assumed.** A finite center and a selected pivot.  No positive-radius
>   hypothesis is needed.
> - **Cited.** None.
> - **Deferred.** Source-domain coverage, multi-pivot analytic transition
>   regularity, source production, branch termination, and all
>   normal-crossing extraction consequences.
> - **Nonclaims.** No full analytic atlas producer, no source coverage, no
>   source-prior theorem, no determinant-chart Haar theorem, no source-rank
>   coverage, no normal-crossing extraction, no pole order, and no RLCT.
> - **Status.** Pen-and-paper reproduction complete; Lean implementation
>   passed focused and full builds; xhigh implementation review passed after
>   documentation repairs.
