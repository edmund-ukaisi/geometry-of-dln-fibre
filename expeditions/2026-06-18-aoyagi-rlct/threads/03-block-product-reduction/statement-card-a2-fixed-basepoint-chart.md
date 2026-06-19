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
>   `DLNFibre.DLN.Aoyagi.rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart`,
>   and
>   `DLNFibre.DLN.Aoyagi.productReduction_chartLocal_suffixStep_fromBlocks_indexed`,
>   `DLNFibre.DLN.Aoyagi.productReduction_chartLocal_suffixChain_blockDiagonal_indexed`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`), plus
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseBasis`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTotalMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrix_self`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrix_proof_irrel`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrix_edge`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrix_succ_right`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTotalMatrix_eq_chainMapMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrix_selfBase`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTotalMatrix_selfBase`,
>   `DLNFibre.DLN.Aoyagi.rank_paperEndpointFixedBaseEdgeMatrix_eq_finrank_range`,
>   `DLNFibre.DLN.Aoyagi.rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_sub`,
>   `DLNFibre.DLN.Aoyagi.rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_range_sub`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBase_chartLocal_suffixStep`,
>   `DLNFibre.DLN.Aoyagi.productReduction_paperEndpointFixedBaseChainMapMatrix_chartLocal_blockDiagonal`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTwoEdgeEdge0Matrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTwoEdgeEdge1Matrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTwoEdgeTotalMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTwoEdgeTotalMatrix_eq_edge1_mul_edge0`,
>   and
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_identityCornerDetChart`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_transformed_identityCornerDetChart`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_selfBase_mem_nhds_transformed_identityCornerDetChart`
>   (`lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`).
> - **Gloss.** The base chain `B` supplies the endpoint adapted bases. The
>   variable chain `C` supplies only the linear maps being represented. The
>   residual block for a variable edge is the Schur complement
>   `A4 - A3 * A1^{-1} * A2`, not the raw lower-right block unless the
>   variable edge is still in identity-corner form.
> - **Proved.** Fixed-basis matrix definitions, chain composition bookkeeping,
>   basepoint equality checks, untransformed and transformed determinant-chart
>   neighborhood membership at `C = B` in ambient matrix space, Schur-residual
>   rank under explicit determinant and rank hypotheses, and the corresponding
>   transformed determinant-chart neighborhood for a single continuous-linear
>   edge parameter at the base edge. Also proved finite product-topology
>   assembly for a fixed prescribed family of accumulated upper blocks
>   `Bprev p`. Also proved a canonical two-edge product wrapper for the first
>   nontrivial composition case. The suffix-step theorem advances one already
>   reduced suffix across a supplied transformed next edge; it is not yet an
>   iterated all-layer induction theorem. The suffix-chain theorem now iterates
>   that step under explicit determinant-chart hypotheses for every transformed
>   edge. The transformed-neighborhood theorem is pointwise in a fixed
>   previously accumulated block `Bprev`.
> - **Assumed.** Finite-dimensional paper-order layers and a supplied
>   total-kernel complement for the base chain. The residual-rank theorem
>   assumes both `identityCornerDetChart` for the variable edge matrix and an
>   exact rank equation for that matrix. The continuous-edge neighborhood
>   theorem additionally assumes a nontrivially normed complete field and
>   topological-vector-space structures on the paper-order layers; the
>   edge-family theorem uses the finite Pi/product topology over `Fin N`.
> - **Cited.** None.
> - **Deferred.** Connecting the fixed-`Bprev` edge-family neighborhood to the
>   upper blocks produced by the suffix-chain induction, source-faithful
>   product/chain neighborhoods, exact rank-stratum packaging, regular
>   coordinate-change certificates, and RLCT consequences.
> - **Kill conditions.** Do not read this as saying rank strata are open or
>   that bases are re-chosen for the variable chain `C`.
