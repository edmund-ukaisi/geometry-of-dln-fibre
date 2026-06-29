# Statement card: A2 retained-passive chart-produced punctured-sector residual-source socket

> **Claim.** On the retained-passive Case 2 determinant-and-pivot-nonzero
> sector, if the chart-produced residual-coordinate marginal has
> selected-entry residual positivity almost everywhere and finite residual
> negative-power integral, then the chart-produced source pushforward satisfies
> the retained-passive p.13 residual-source positivity and integrability
> hypotheses on the local source.
>
> - **Lean:** target
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_marginal`
>   (`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean` @ `f82c8076`)
> - **Gloss.** The theorem calls the existing punctured-sector readout theorem
>   to get an open sector `V`.  For
>   `mu = Measure.map sourceChart (sourceMeasure.restrict V)` and
>   `marginal = Measure.map Prod.snd (sourceMeasure.restrict V)`, it proves
>   `mu.restrict localSource = mu` and turns explicit positivity and
>   integrability assumptions on `marginal` for
>   `SelectedEntrySignedBox.CenterCoord.residual pivotNext` into the
>   corresponding fixed-base residual positivity and
>   `residualNegPowerIntegrableOn` statement for `mu`.
> - **Proved.** Lean proves the chart-produced source measure is supported on
>   the retained-passive p.13 local source and, under explicit marginal
>   positivity and finite-integral assumptions, satisfies the corresponding
>   source-side residual positivity and `residualNegPowerIntegrableOn`
>   conclusion.
> - **Assumed.** The marginal positivity and marginal finite negative-power
>   integral hypotheses remain explicit.  The source measure is arbitrary.
> - **Cited.** None.
> - **Deferred.** No determinant-chart Haar transport, raw/source Haar theorem,
>   external/original source-prior comparison, passive Jacobian formula,
>   source-image equality, source-rank coverage, normal crossings, pole order,
>   or RLCT extraction.
> - **Structure & ideas observed.** The fixed-pivot inverse is only an inverse
>   after the pivot coordinate is nonzero.  Marginal positivity of the
>   selected-entry residual implies this nonzero pivot condition almost
>   everywhere after pulling back by `inverseReadout`; on that a.e. set, the
>   source residual square-sum is exactly the selected-entry residual of the
>   inverse readout, up to the finite residual-coordinate reindexing.
> - **Route.** Use the existing map identity
>   `Measure.map inverseReadout mu = marginal`, `ae_of_ae_map`, the
>   selected-entry `chartMap_preimageOfPivotNeZero` and
>   `chartMap_eq_zero_of_pivot_eq_zero` lemmas, finite square-sum reindexing,
>   `lintegral_map`, and `lintegral_congr_ae`.  Rewrite the final source
>   restriction by the support equality `mu.restrict localSource = mu`.
> - **Status.** sorry-free + reviewed.
