# Statement card: A2 selected-entry one-chart analytic predicate data

> **Claim.** For a fixed selected-entry pivot, the already proved one-chart
> chart, identity-transition, unit, and Jacobian/volume data inhabit the
> corresponding forgetful analytic predicates for the finite selected-entry
> normal-crossing certificate.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.SelectedEntryOneChartAnalyticPredicateData`.
> - **Gloss.** The forgetful predicates have shape
>   `exists ctx, Nonempty (data ctx)`.  The witness context is
>   `selectedEntryOneChartAnalyticAtlasContext pivot`, and the data witnesses
>   are the one-chart records already proved in the preceding checkpoints.
> - **Proved.**
>   `selectedEntryOneChartAnalyticChartRegular`,
>   `selectedEntryOneChartAnalyticTransitionRegular`,
>   `selectedEntryOneChartAnalyticUnitRegular`, and
>   `selectedEntryOneChartAnalyticJacobianVolumeCompatible`.
> - **Assumed.** A finite center and selected pivot.  Positive radii
>   `forall i, 0 < R i` are needed only for the Jacobian/volume-compatible
>   predicate, inherited from `selectedEntryOneChartAnalyticJacobianVolumeData`.
> - **Cited.** None.
> - **Deferred.** Source-domain coverage, a full supplied analytic atlas
>   producer, source production, branch termination, and all
>   normal-crossing extraction consequences.
> - **Nonclaims.** No source coverage, no full analytic atlas producer, no
>   source-prior theorem, no determinant-chart Haar theorem, no source-rank
>   coverage, no normal-crossing extraction, no pole order, and no RLCT.
> - **Status.** Pen-and-paper reproduction complete; focused Lean build passed;
>   xhigh source/scope and Lean/API reviews passed.
