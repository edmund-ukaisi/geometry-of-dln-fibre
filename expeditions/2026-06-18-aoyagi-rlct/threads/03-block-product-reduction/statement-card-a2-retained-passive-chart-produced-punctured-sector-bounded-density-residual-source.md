# Statement card: A2 retained-passive chart-produced punctured-sector bounded-density residual source

> **Claim.** For a source measure supplied as a density with respect to the
> passive-product selected-entry weighted-box measure, each finite scalar
> `c : ENNReal` that bounds that density a.e. on the returned punctured sector
> implies the retained-passive residual-source hypotheses.
>
> - **Lean:** target
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass`
>   (`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`);
>   helper
>   `DLNFibre.DLN.Aoyagi.restrict_withDensity_le_smul_of_ae_le`
>   (`lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`).
> - **Gloss.** The theorem sets
>   `sourceMeasure = passiveSource.withDensity sourceDensity`, calls the
>   local-domination residual-source wrapper to choose the open sector `V`,
>   and uses a local density bound
>   `sourceDensity <= c` a.e. for `passiveSource.restrict V` to prove
>   `(passiveSource.withDensity sourceDensity).restrict V <= c • passiveSource`.
>   The residual conclusion is explicitly conditional:
>   `forall {c : ENNReal}, c < infinity ->
>   (forall a.e. z with respect to passiveSource.restrict V,
>   density z <= c) -> ...`.
> - **Proved.** Lean should prove `mu.restrict localSource = mu`
>   unconditionally from the socket, and under the local bounded-density
>   assumption prove residual positivity a.e. plus
>   `residualNegPowerIntegrableOn localSource mu t`, where
>   `mu = Measure.map sourceChart ((passiveSource.withDensity sourceDensity).restrict V)`.
> - **Assumed.** The source density and its finite local a.e. bound are
>   explicit inputs.  The passive measure has finite total mass.  The exponent
>   satisfies `0 <= t` and the selected-entry critical inequality.  The
>   signed-box radii are strictly positive.  The usual Case 2 retained-passive
>   continuity and base determinant/pivot hypotheses are assumed.
> - **Cited.** None.
> - **Deferred.** No proof that an external/original source prior admits this
>   density or bound; no determinant-chart Haar transport, raw/source Haar
>   theorem, passive Jacobian formula, source-image equality, source-rank
>   coverage, normal crossings, pole order, or RLCT extraction.
> - **Route.** Prove the generic helper by `restrict_withDensity`,
>   `withDensity_mono`, `withDensity_const`, and
>   `measure_le_smul_of_le_smul_restrict`; then feed the resulting local
>   domination into the banked local-domination residual-source theorem.
> - **Status.** helper and Aoyagi wrapper implemented.  Focused handoff build
>   and full `DLNFibre` build passed via `scripts/lb`; `scripts/sorries`,
>   `git diff --check`, touched Lean-file forbidden-marker scan, and direct
>   axiom probes passed with `[propext, Classical.choice, Quot.sound]`.  Xhigh
>   route review and xhigh post-implementation review PASS in
>   `review-a2-retained-passive-chart-produced-punctured-sector-bounded-density-residual-source.md`.
