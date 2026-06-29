# Statement card: A2 retained-passive chart-produced punctured-sector local-domination residual source

> **Claim.** For an arbitrary coordinate-domain source measure, the
> punctured-sector residual-source hypotheses follow from an explicit local
> domination of `sourceMeasure.restrict V` by a finite scalar multiple of the
> passive-product selected-entry weighted-box measure, together with finite
> passive mass and the selected-entry critical inequality.
>
> - **Lean:** target
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_restrict_le_smul_passiveProductMeasure_finiteMass`
>   (`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`)
> - **Gloss.** The theorem calls the residual-source socket with arbitrary
>   `sourceMeasure` to get an open punctured sector `V`.  Inside the returned
>   sector, if
>   `sourceMeasure.restrict V <= c • (passiveMeasure.prod weightedBox)` with
>   `c < infinity`, then the socket's marginal hypotheses follow by mapping
>   this domination through `Prod.snd`, first comparing the passive product
>   marginal to `weightedBox`, then comparing the arbitrary source marginal to
>   that passive product marginal.
> - **Proved.** Lean should prove `mu.restrict localSource = mu`
>   unconditionally from the socket, and under the local domination assumption
>   prove source-side residual positivity almost everywhere on
>   `mu.restrict localSource` plus
>   `residualNegPowerIntegrableOn localSource mu t`, where
>   `mu = Measure.map sourceChart (sourceMeasure.restrict V)`.
> - **Assumed.** The local domination field is explicit and appears after `V`
>   is chosen.  The passive measure has finite total mass.  The scalar `c` is
>   finite.  The exponent satisfies `0 <= t` and
>   `2 * t < ((center.erase pivotNext.1).card : R) + 1`.  Signed-box radii are
>   strictly positive.  The usual Case 2 retained-passive continuity and base
>   determinant/pivot hypotheses are assumed.
> - **Cited.** None.
> - **Deferred.** No proof that an external/original source prior satisfies the
>   local domination field; no determinant-chart Haar transport, raw/source
>   Haar theorem, passive Jacobian formula, source-image equality, source-rank
>   coverage, normal crossings, pole order, or RLCT extraction.
> - **Structure & ideas observed.** The proof uses two scalar-domination
>   transfers.  First, `Measure.map Prod.snd (passiveMeasure.prod weightedBox)`
>   is `passiveMeasure Set.univ • weightedBox`, so raw selected-entry residual
>   facts transfer to the passive product marginal.  Second, local source-domain
>   domination maps to residual-marginal domination, so those facts transfer to
>   the arbitrary source marginal.
> - **Route.** Use the residual-source socket.  Use `Measure.map_snd_prod` for
>   the passive product marginal, `map_le_smul_map_of_le_smul measurable_snd`
>   for the arbitrary source domination, and transfer a.e. positivity / finite
>   lower integrals by `ae_of_measure_le_smul` and
>   `lintegral_lt_top_of_measure_le_smul`.  Feed the resulting marginal facts
>   to the socket.
> - **Status.** proved sorry-free in Lean; xhigh post-implementation review
>   PASS in
>   `review-a2-retained-passive-chart-produced-punctured-sector-local-domination-residual-source.md`;
>   focused build, full `DLNFibre` build, `scripts/sorries`,
>   `git diff --check`, touched-file forbidden-marker scan, and direct axiom
>   probe passed with `[propext, Classical.choice, Quot.sound]`.
