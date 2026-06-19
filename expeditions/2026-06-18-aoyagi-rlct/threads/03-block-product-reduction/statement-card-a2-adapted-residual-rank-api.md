# Statement card - A2 adapted residual rank API

> **Claim.** The deterministic suffix state exposes the Schur residual blocks
> it actually visits, and those transformed residual blocks have the expected
> pointwise rank under explicit determinant-chart and exact-rank hypotheses.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.residualBlock`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_D_self`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_D_castSucc`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`), and
>   `DLNFibre.DLN.Aoyagi.rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range`,
>   `DLNFibre.DLN.Aoyagi.rank_schurResidualBlock_transformed_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_range_sub`,
>   `DLNFibre.DLN.Aoyagi.rank_transformedEdge_fixedBaseReverseEdges_eq_range_sub`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdgesRecursiveResidualRankImplications`,
>   and
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_rankImp_mem_nhds`
>   (`lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`).
> - **Gloss.** The residual block is
>   `schurResidualBlock ([I Bprev; 0 I] * E p)` for the actual recursive
>   suffix state. The `D` field updates by multiplying this adapted residual
>   block.
> - **Proved.** The terminal `D` block is identity, the recursive `D` block
>   unfolds by multiplying the next visited residual, and the transformed
>   residual has rank `rank(E p) - finrank(U0)` when the transformed edge lies
>   in the determinant chart. Near a continuous edge family based at
>   `reverseEdge W B`, recursive determinant charts, endpoint block form, and
>   the residual-rank implications hold on one neighborhood.
> - **Assumed.** Determinant-chart membership for the transformed edge and
>   exact pointwise rank of the edge map. The fixed-base rank bridge identifies
>   matrix rank with `finrank (LinearMap.range (E p))`.
> - **Cited.** None.
> - **Deferred.** A closed dependent product of all residual blocks, exact-rank
>   neighborhoods, and source-facing certificate transport.
> - **Kill conditions.** Do not treat this as a raw product of untransformed
>   edge Schur residuals or as a proof that exact-rank strata are open.
