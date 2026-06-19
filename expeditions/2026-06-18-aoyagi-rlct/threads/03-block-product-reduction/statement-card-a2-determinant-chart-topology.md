# Statement card - A2 determinant chart topology

> **Claim.** The selected top-left determinant chart is open, so an adapted
> identity-corner matrix has a neighborhood remaining in that chart.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.isOpen_identityCornerDetChart`,
>   `DLNFibre.DLN.Aoyagi.identityCornerDetChart_mem_nhds`,
>   `DLNFibre.DLN.Aoyagi.leftMul_identityCornerDetChart_mem_nhds`,
>   `DLNFibre.DLN.Aoyagi.fromBlocks_leftMul_identityCornerDetChart_mem_nhds`,
>   `DLNFibre.DLN.Aoyagi.continuous_linearMap_toMatrix`,
>   `DLNFibre.DLN.Aoyagi.identityCornerForm_mem_nhds_identityCornerDetChart`,
>   `DLNFibre.DLN.Aoyagi.paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart`,
>   and
>   `DLNFibre.DLN.Aoyagi.unitriangular_paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart`
>   (`lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`), with fixed-base wrappers
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart`
>   and
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_selfBase_mem_nhds_transformed_identityCornerDetChart`
>   and
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_variableBprev_mem_nhds_transformed_identityCornerDetChart`
>   (`lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`).
> - **Gloss.** The top-left block projection and determinant are continuous
>   functions of the matrix entries, and the unit locus is open under
>   `IsOpenUnits`.
> - **Proved.** Topological determinant-chart openness, neighborhood
>   membership for adapted paper edges and their upper-unitriangular transforms,
>   matrix-space pullback of the chart under fixed left multiplication, and
>   continuity of the fixed-basis matrix-coordinate map on continuous linear
>   maps. Also proved finite Pi-topology assembly of the fixed-base
>   continuous-edge neighborhoods for a prescribed family of transformed charts,
>   and the parameter-space continuity handoff for continuously varying
>   transformed charts.
> - **Assumed.** `CommRing`, topological ring, and open-units hypotheses for
>   determinant-chart openness; finite-dimensional layers for the paper
>   adapted-edge wrappers; nontrivially normed complete field and target
>   topological-vector-space hypotheses for the continuous-linear-map
>   coordinate theorem.
> - **Cited.** None.
> - **Deferred.** Exact rank-stratum topology, source-faithful
>   product/chain-neighborhood assembly beyond continuous supplied transformed
>   charts, deterministic construction of the induction-produced chart data,
>   analytic coordinate changes, and RLCT consequences.
> - **Kill conditions.** Do not read this as saying rank strata are open, or
>   that the adapted bases are fixed across a neighborhood of variable chains.
