# Statement card: A2 retained-passive topology-tuple punctured-sector transport

> **Claim.** On a punctured determinant sector for the with-passive Case 2
> selected-entry chart, the topology-tuple raw-order p.13 source chart presents
> the same chart-produced source edge family as the direct retained-passive
> source chart, and the selected-entry inverse readout recovers the residual
> coordinates.
>
> - **Lean:** target
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_case2EndpointTransport_withPassive_topologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq`
>   in
>   `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean`.
> - **Gloss.** The theorem defines
>   `retainedData z` as the endpoint transport of the with-passive Case 2
>   selected-entry datum, `sourceChart z` as the direct fixed-base p.13 source
>   edge family of that datum, `y = topologyTuple (retainedData z)`, and
>   `raw = topologyTupleEdgeRawOrder y`.  It returns an open sector `V` such
>   that for every `z in V`, `y` lies in `topologyTupleDetChartSet`, `raw` lies
>   in `topologyTupleRawOrderSourceRecursiveDetChartSet`,
>   `paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart raw =
>   sourceChart z`, source readback recovers `retainedData z`, and
>   `inverseReadout (sourceChart z) = z.2`.
> - **Proved.** Pointwise topology/raw-order source-chart agreement, local
>   determinant-chart and raw-order chart membership, retained-passive local
>   source membership, source-readback equality, and selected-entry inverse
>   readout equality on the returned punctured sector.
> - **Assumed.** The usual Case 2 bounds `hS`, `hcont`, `hnext`; supplied
>   endpoint equivalences `eNext` and `e`; continuity of the passive fields;
>   determinant-unit hypotheses at the basepoint for `Ctop` and `A1passive`;
>   and the basepoint selected-pivot nonzero hypothesis.
> - **Cited.** None.
> - **Deferred.** This does not prove source-image equality, source-rank
>   coverage, determinant-chart Haar transport, raw/source Haar transport,
>   external/original source-prior comparison, a measure pushforward theorem,
>   a Jacobian formula, normal crossings, pole order, or RLCT extraction.
> - **Route.** Use the existing open source-readback and punctured readout
>   theorem, derive `retainedData z` lies in the determinant chart from local
>   source membership and source readback, convert to topology tuple
>   determinant membership, use the raw-order maps-to theorem, apply the
>   generic raw-order source-chart identity, and reuse the selected-entry
>   inverse readout equality on the pivot-nonzero sector.
> - **Status.** implemented; focused build of
>   `DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySource`
>   passed via `scripts/lb`.  Xhigh Lean/API scout `Locke the 4th` and xhigh
>   source-scope scout `Laplace the 4th` endorsed the route and nonclaim
>   boundary.  Xhigh implementation review by `Singer the 4th` PASS.
