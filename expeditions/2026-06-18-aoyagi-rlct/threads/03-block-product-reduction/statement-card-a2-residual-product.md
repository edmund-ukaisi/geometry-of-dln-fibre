# Statement card - A2 residual product

> **Claim.** The deterministic suffix-state lower-right block is the ordered
> product of the transformed Schur residual blocks visited by the suffix
> recursion, and the fixed-base endpoint certificate can expose this product
> in the Aoyagi triangular block-diagonal form.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.residualProduct`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.residualProduct_self`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.residualProduct_castSucc`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_D_eq_residualProduct`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal_residualProduct`,
>   `DLNFibre.DLN.Aoyagi.productReduction_chartLocal_suffixChain_triangularBlockDiagonal_residualProduct_indexed`,
>   and
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct`.
> - **Gloss.** Aoyagi's induction updates the lower-right endpoint block by
>   multiplying the previous residual product by the Schur residual of the
>   next transformed layer. Lean names that deterministic product and rewrites
>   the already-proved endpoint `D` field as that product.
> - **Proved.** Identity at the right endpoint; one-step product unfolding;
>   equality between `suffixState.D` and the residual product; triangular
>   block-diagonal wrappers with lower-right block equal to the named product;
>   fixed-base endpoint certificate wrapper.
> - **Assumed.** The same determinant-chart hypotheses as the existing
>   suffix-chain and fixed-base certificate layers. The abstract all-layer
>   wrapper keeps the older all-`Bprev` chart assumption.
> - **Cited.** None.
> - **Review.** xhigh endpoint scout `Copernicus` confirmed the endpoint
>   wrapper shape; xhigh Lean/math reviewer `Pascal` passed the
>   residual-product slice with one non-blocking scope note. See
>   `review-a2-residual-product.md`.
> - **Deferred.** Weakening the abstract chart hypothesis to only recursively
>   visited `Bprev` values; chart coverage from only source rank hypotheses;
>   exact-rank openness; Aoyagi Lemma 1; analytic ideal transport; regular
>   coordinate RLCT bookkeeping; normal crossings; all RLCT claims.
> - **Kill conditions.** Do not identify the product with the raw lower-right
>   edge-block product. Do not read the endpoint wrapper as chart coverage,
>   exact-rank openness, normal crossings, or an RLCT statement.
