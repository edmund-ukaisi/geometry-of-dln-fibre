# Statement card - A2 endpoint-compatible chart data

> **Claim.** Finite-dimensional chains admit supplied adapted bases in which
> every edge still has `[I B; 0 D]` form and the total product has
> `[I 0; 0 0]` form using the same endpoint-compatible basis family.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedBasis`,
>   `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_adaptedBasis_eq_fromBlocks_one_zero`,
>   `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_chartData_eq_fromBlocks_one_zero_zero_of_maps_complement_to_zero`,
>   `DLNFibre.DLN.Aoyagi.throughSubspaceEndpointComplement`,
>   `DLNFibre.DLN.Aoyagi.throughSubspaceEndpointComplementIndex`,
>   `DLNFibre.DLN.Aoyagi.throughSubspaceEndpointChartDataOfFiniteDimensional`,
>   `DLNFibre.DLN.Aoyagi.exists_isCompl_ker_throughSubspaceEndpointChartDataOfFiniteDimensional`,
>   `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_endpointChartData_eq_fromBlocks_one_zero_zero`,
>   `DLNFibre.DLN.Aoyagi.endpointChartData_edge_and_totalProduct_blocks`,
>   `DLNFibre.DLN.Aoyagi.exists_isCompl_ker_paperEndpointChartDataOfFiniteDimensional`,
>   and
>   `DLNFibre.DLN.Aoyagi.paperEndpointChartData_edge_and_totalProduct_blocks`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** `throughSubspaceAdaptedBasis` names the ambient basis at every
>   vertex from one supplied `ThroughSubspaceChartData` bundle. The generic
>   endpoint theorem only assumes that the source complement `data.W 0` maps to
>   zero under the total chain map. The finite endpoint-compatible construction
>   chooses `data.W 0` to be the total kernel and arbitrary complements at the
>   other vertices. Paper-order wrappers instantiate this on the reversed
>   Aoyagi chain and state the total-product block form for `paperChainMap`.
> - **Proved.** Shared-basis edge block form, shared-basis total-product block
>   form, finite existence of endpoint-compatible chart data, and a one-edge
>   package combining an edge block with the total-product block in the same
>   basis family.
> - **Assumed.** Field-vector-space hypotheses and finite-dimensional layers
>   for the finite existence wrappers; an `IsCompl U0 (ker P)` hypothesis for a
>   fixed endpoint-compatible data bundle.
> - **Cited.** None.
> - **Deferred.** Proving that the ordered product of the edge matrices equals
>   the total matrix in these shared bases; iterating right elimination through
>   all layers; rank/open-neighborhood statements; and every analytic/RLCT
>   consequence.
> - **Kill conditions.** This is still adapted-coordinate bookkeeping. It does
>   not prove Aoyagi Theorem 3, rank preservation, local openness, or any
>   normal-crossing/RLCT statement.
