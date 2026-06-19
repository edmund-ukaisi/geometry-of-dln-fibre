# Statement card - A2 determinant chart topology

> **Claim.** The selected top-left determinant chart is open, so an adapted
> identity-corner matrix has a neighborhood remaining in that chart.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.isOpen_identityCornerDetChart`,
>   `DLNFibre.DLN.Aoyagi.identityCornerDetChart_mem_nhds`,
>   `DLNFibre.DLN.Aoyagi.leftMul_identityCornerDetChart_mem_nhds`,
>   `DLNFibre.DLN.Aoyagi.fromBlocks_leftMul_identityCornerDetChart_mem_nhds`,
>   `DLNFibre.DLN.Aoyagi.identityCornerForm_mem_nhds_identityCornerDetChart`,
>   `DLNFibre.DLN.Aoyagi.paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart`,
>   and
>   `DLNFibre.DLN.Aoyagi.unitriangular_paperAdaptedReverseEdgeMatrix_mem_nhds_identityCornerDetChart`
>   (`lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`).
> - **Gloss.** The top-left block projection and determinant are continuous
>   functions of the matrix entries, and the unit locus is open under
>   `IsOpenUnits`.
> - **Proved.** Topological determinant-chart openness, neighborhood
>   membership for adapted paper edges and their upper-unitriangular transforms,
>   and matrix-space pullback of the chart under fixed left multiplication.
> - **Assumed.** `CommRing`, topological ring, and open-units hypotheses for
>   the base ring; finite-dimensional layers for the paper adapted-edge
>   wrappers.
> - **Cited.** None.
> - **Deferred.** Exact rank-stratum topology, pulling these matrix
>   neighborhoods back to a topology on variable chains, analytic coordinate
>   changes, and RLCT consequences.
> - **Kill conditions.** Do not read this as saying rank strata are open, or
>   that the adapted bases are fixed across a neighborhood of variable chains.
