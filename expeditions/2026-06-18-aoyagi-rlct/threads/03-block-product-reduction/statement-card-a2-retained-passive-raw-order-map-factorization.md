# Statement card: A2 retained-passive raw-order map factorization

> **Claim.** On the punctured sector for the with-passive Case 2 selected-entry
> chart, the chart-produced source pushforward equals the pushforward by the
> raw-order source-chart composite.
>
> - **Lean:** target
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_comp_eq_sourceChart_inverseReadout_eq_snd`
>   in
>   `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasure.lean`.
> - **Gloss.** The theorem defines
>   `rawMap z = topologyTupleEdgeRawOrder (topologyTuple (retainedData z))`
>   and `rawChart` as the public raw-order p.13 source chart.  It returns an
>   open sector `V` such that `rawChart (rawMap z) = sourceChart z` for every
>   `z in V`, hence
>   `Measure.map (fun z => rawChart (rawMap z)) (sourceMeasure.restrict V) =
>   Measure.map sourceChart (sourceMeasure.restrict V)`.  It also keeps the
>   pointwise local-source membership, source-readback equality, and
>   selected-entry inverse readout on `V`.
> - **Proved.** One-stage raw-order composite pushforward equality over the
>   restricted sector, pointwise raw-order chart membership and source-chart
>   equality, local-source membership, source-readback equality, and
>   selected-entry inverse readout.
> - **Assumed.** Same hypotheses as the topology-tuple punctured-sector
>   transport theorem: Case 2 bounds, endpoint equivalences, passive-field
>   continuity, determinant-unit hypotheses at the basepoint, basepoint pivot
>   nonzero, and an arbitrary coordinate-domain source measure.
> - **Cited.** None.
> - **Deferred.** The two-stage equality through
>   `Measure.map rawChart (Measure.map rawMap ...)` is deferred until the
>   raw-order intermediate-measure a.e. measurability is needed by a consumer.
> - **Nonclaims.** No new Aoyagi calculation; no determinant-chart Haar
>   transport, raw/source Haar theorem, external/original source-prior
>   comparison, passive Jacobian formula, density identity, source-image
>   equality, source-rank coverage, normal crossings, pole order, or RLCT
>   extraction.
> - **Status.** Lean implemented; focused/full builds and gates passed;
>   implementation review PASS after documentation scope repair.
