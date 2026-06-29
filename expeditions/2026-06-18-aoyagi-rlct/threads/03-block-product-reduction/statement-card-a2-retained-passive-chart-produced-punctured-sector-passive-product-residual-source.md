# Statement card: A2 retained-passive chart-produced punctured-sector passive-product residual source

> **Claim.** For the concrete passive selected-entry coordinate-domain measure
> `passiveMeasure.prod weightedBox`, where `weightedBox` is the selected-entry
> signed box with Aoyagi's source density, the open punctured-sector
> chart-produced source measure satisfies the retained-passive p.13
> residual-source positivity and negative-power integrability hypotheses,
> assuming finite passive mass and the selected-entry critical inequality.
>
> - **Lean:** proved
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass`
>   (`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`)
> - **Gloss.** The theorem calls the residual-source socket to get an open
>   determinant-and-pivot-nonzero sector `V`.  For
>   `sourceMeasure = passiveMeasure.prod weightedBox`, it proves the socket's
>   marginal residual positivity and finite negative-power integral by
>   dominating
>   `Measure.map Prod.snd (sourceMeasure.restrict V)` by
>   `passiveMeasure Set.univ • weightedBox`, then applying the selected-entry
>   signed-box residual theorem and finite passive mass.
> - **Proved.** Lean proves `mu.restrict localSource = mu`, source-side
>   residual positivity almost everywhere on `mu.restrict localSource`, and
>   `residualNegPowerIntegrableOn localSource mu t` for
>   `mu = Measure.map sourceChart ((passiveMeasure.prod weightedBox).restrict V)`.
> - **Assumed.** The passive measure has finite total mass.  The exponent
>   satisfies `0 <= t` and
>   `2 * t < ((center.erase pivotNext.1).card : R) + 1`.  Signed-box radii are
>   strictly positive.  The usual Case 2 retained-passive continuity and base
>   determinant/pivot hypotheses are assumed.
> - **Cited.** None.
> - **Deferred.** No determinant-chart Haar transport, raw/source Haar theorem,
>   external/original source-prior comparison, passive Jacobian formula,
>   source-image equality, source-rank coverage, normal crossings, pole order,
>   or RLCT extraction.
> - **Structure & ideas observed.** Sector restriction only gives domination of
>   the residual-coordinate marginal by the unrestricted product marginal:
>   `Measure.map Prod.snd ((passiveMeasure.prod weightedBox).restrict V) <=
>   passiveMeasure Set.univ • weightedBox`.  Equality would be false for a
>   general sector.  This domination is enough to transfer a.e. positivity and
>   finite lower integrals from `weightedBox`.
> - **Route.** Use the already-proved residual-source socket.  Inside its
>   returned `V`, prove marginal domination by `Measure.map_mono
>   Measure.restrict_le_self measurable_snd` and `Measure.map_snd_prod`.
>   Obtain the weighted-box residual facts from
>   `SelectedEntrySignedBox.CenterCoord.residual_pos_ae_and_lintegral_rpow_neg_withDensity_sourceDensity`.
>   Transfer them to the sector marginal with `ae_of_measure_le_smul` and
>   `lintegral_lt_top_of_measure_le_smul`, then feed them to the socket.
> - **Status.** sorry-free + reviewed.  Focused and full builds passed via
>   `scripts/lb`; `scripts/sorries`, `git diff --check`, touched Lean-file
>   forbidden-marker scan, and direct axiom probe passed.  Xhigh route review
>   by `Cicero the 3rd` and implementation review by `Epicurus the 3rd`
>   returned PASS.  Direct axiom probe:
>   `[propext, Classical.choice, Quot.sound]`.
