# Statement card: A2 retained-passive raw-order two-stage pushforward

> **Claim.** On the punctured sector for the with-passive Case 2
> selected-entry chart, the chart-produced source pushforward equals both the
> one-stage raw-order source-chart composite pushforward and the two-stage
> pushforward through the intermediate raw-order tuple measure.
>
> - **Lean:** target
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_twoStage_eq_sourceChart_inverseReadout_eq_snd`
>   in
>   `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean`.
> - **Gloss.** With
>   `rawMap z = topologyTupleEdgeRawOrder (topologyTuple (retainedData z))`
>   and `rawChart` the public raw-order p.13 source chart, the theorem returns
>   an open sector `V` such that `rawChart (rawMap z) = sourceChart z` for
>   every `z in V`.  It proves, for `nu = sourceMeasure.restrict V`, that
>   `Measure.map (fun z => rawChart (rawMap z)) nu =
>   Measure.map sourceChart nu` and
>   `Measure.map rawChart (Measure.map rawMap nu) =
>   Measure.map sourceChart nu`.
> - **Proved.** Sector-restricted one-stage and two-stage raw-order pushforward
>   equalities; local a.e. measurability of `rawMap`; local a.e. measurability
>   of `rawChart` after support on the raw-order determinant target; pointwise
>   raw-order chart membership, source-chart equality, local-source membership,
>   source-readback equality, and selected-entry inverse readout.
> - **Assumed.** Same Case 2 bounds, endpoint equivalences, passive-field
>   continuity, determinant-unit basepoint hypotheses, basepoint pivot-nonzero
>   hypothesis, and arbitrary coordinate-domain source measure as the one-stage
>   theorem.  The measure conclusion additionally assumes Borel measurable
>   structures on the raw-order topology-tuple target and edge-family target.
> - **Cited.** None.  The Aoyagi source formulas are inherited from the already
>   reproduced p.13 retained-passive and selected-entry sector checkpoints.
> - **Deferred.** No source-prior comparison, Haar/Jacobian transport, chart
>   coverage, normal-crossing extraction, pole order, or RLCT statement.
> - **Nonclaims.** No new Aoyagi calculation; no determinant-chart Haar
>   transport, raw/source Haar theorem, external/original source-prior
>   comparison, passive Jacobian formula, density identity, source-image
>   equality, source-rank coverage, normal crossings, pole order, or RLCT
>   extraction.
> - **Status.** Lean implemented; focused/full builds and gates passed; xhigh
>   source-scope and Lean/API reviews PASS.
