# Statement card - A2 fixed-basepoint variable chart

> **Claim.** Once an endpoint chart is fixed from a base paper-order chain `B`,
> any variable chain `C` can be expressed in those same fixed bases. In those
> coordinates, chain-segment matrices compose in the expected order; at `C = B`
> they recover the endpoint adapted basepoint matrices; and, under explicit
> determinant-chart and exact-rank hypotheses, the selected Schur residual of a
> variable edge has rank `rho - r`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.lowerLeftBlock`,
>   `DLNFibre.DLN.Aoyagi.fromBlocks_corners`,
>   `DLNFibre.DLN.Aoyagi.schurResidualBlock`,
>   `DLNFibre.DLN.Aoyagi.rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`), plus
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseBasis`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTotalMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrix_self`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrix_edge`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrix_succ_right`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTotalMatrix_eq_chainMapMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrix_selfBase`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTotalMatrix_selfBase`,
>   `DLNFibre.DLN.Aoyagi.rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_sub`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTwoEdgeEdge0Matrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTwoEdgeEdge1Matrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTwoEdgeTotalMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTwoEdgeTotalMatrix_eq_edge1_mul_edge0`,
>   and
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_identityCornerDetChart`
>   (`lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`).
> - **Gloss.** The base chain `B` supplies the endpoint adapted bases. The
>   variable chain `C` supplies only the linear maps being represented. The
>   residual block for a variable edge is the Schur complement
>   `A4 - A3 * A1^{-1} * A2`, not the raw lower-right block unless the
>   variable edge is still in identity-corner form.
> - **Proved.** Fixed-basis matrix definitions, chain composition bookkeeping,
>   basepoint equality checks, determinant-chart neighborhood membership at
>   `C = B`, Schur-residual rank under explicit determinant and rank
>   hypotheses, and a canonical two-edge product wrapper for the first
>   nontrivial composition case.
> - **Assumed.** Finite-dimensional paper-order layers and a supplied
>   total-kernel complement for the base chain. The residual-rank theorem
>   assumes both `identityCornerDetChart` for the variable edge matrix and an
>   exact rank equation for that matrix.
> - **Cited.** None.
> - **Deferred.** Iterating the Schur product-reduction induction, proving
>   determinant-chart hypotheses on an actual chain neighborhood, exact
>   rank-stratum packaging, regular coordinate-change certificates, and RLCT
>   consequences.
> - **Kill conditions.** Do not read this as saying rank strata are open or
>   that bases are re-chosen for the variable chain `C`.
