# Statement card - A2 paper-order finite edge block

> **Claim.** In finite-dimensional paper-order chains, each reversed paper edge
> has concrete adapted-basis block form `[I B; 0 D]`, this form survives the
> local upper-unitriangular chart transformation, and the total paper product
> has endpoint block form `[I 0; 0 0]`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap`,
>   `DLNFibre.DLN.Aoyagi.isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap`,
>   `DLNFibre.DLN.Aoyagi.exists_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`,
>   `DLNFibre.DLN.Aoyagi.exists_unitriangular_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`,
>   and
>   `DLNFibre.DLN.Aoyagi.toMatrix_paperChainMap_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
>   The generic chart predicate layer is
>   `DLNFibre.DLN.Aoyagi.topLeftCorner`,
>   `DLNFibre.DLN.Aoyagi.identityCornerForm`,
>   `DLNFibre.DLN.Aoyagi.identityCornerDetChart`,
>   `DLNFibre.DLN.Aoyagi.topLeftCorner_eq_one_of_identityCornerForm`,
>   and
>   `DLNFibre.DLN.Aoyagi.identityCornerDetChart_of_identityCornerForm`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`).
>   The one-edge right-elimination wrapper is
>   `DLNFibre.DLN.Aoyagi.productReduction_paperAdaptedReverseEdgeMatrix_rightElim`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** The theorem applies the finite through-layer block theorem to the
>   reversed paper chain `reverseVertex W`, `reverseEdge W B`. The hypothesis is
>   phrased against the paper-order total product `paperChainMap`; the helper
>   theorem converts it to the source-to-target total-kernel or complement
>   hypothesis by `chainMap_reverse_eq_paper`. The named adapted edge matrix
>   `paperAdaptedReverseEdgeMatrix` is shown to have `identityCornerForm`, hence
>   selected top-left corner `1` and algebraic determinant-chart membership.
> - **Proved.** Concrete finite-basis per-edge `[I B; 0 D]` form and
>   unitriangular chart-form preservation for paper-order edges viewed through
>   the reversed chain; endpoint `[I 0; 0 0]` form for the total paper product
>   when the source complement is the total kernel. Also proved determinant
>   chart membership for the adapted paper edge matrix and its unitriangular
>   transform, plus one-edge right elimination for a block-diagonal prefix
>   followed by one adapted paper edge.
> - **Assumed.** Field-vector-space hypotheses, finite-dimensional layers, and a
>   through-subspace disjointness hypothesis for the paper-order total product.
> - **Cited.** None.
> - **Deferred.** Endpoint-compatible shared adapted bases; product-reduction
>   induction assembly; topological open-neighborhood statements; and every
>   analytic/RLCT consequence.
> - **Kill conditions.** This is adapted-coordinate bookkeeping. It does not
>   state that Aoyagi's fixed coordinate blocks are invertible, prove rank
>   preservation, or prove Theorem 3. The determinant-chart predicate is
>   algebraic `IsUnit` at the adapted base matrix, not a topology statement.
>   The concrete finite edge wrappers are not yet a composable all-layer product
>   assembly with the endpoint theorem.
