# Statement card - A2 rank-stratum boundary

> **Claim.** The fixed-base product-reduction certificate can be restricted to
> Aoyagi's exact layer-rank stratum without asserting that the stratum is open.
> On that stratum, the residual-rank implications become residual-rank
> equalities; on the source-shaped rank stratum with base product rank `r`,
> the visited residual block has rank `rEdge p - r`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeRankStratum`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseSourceRankStratum`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdgesRecursiveResidualRanks`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionRankStratumCertificate`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionCertificate.residualRanks_of_edgeRankStratum`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionCertificate.rankStratumCertificate`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionCertificate.residualBlock_rank_eq_sourceRankSubProductRank`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin_source`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate.mem_nhdsWithin_source`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointProductReductionRankStratumLocalCertificate`,
>   and
>   `DLNFibre.DLN.Aoyagi.exists_paperEndpointProductReductionRankStratumLocalCertificate`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`).
> - **Gloss.** The exact edge-rank stratum records
>   `finrank range(Cedge x p) = rEdge p` for every layer.  The source-shaped
>   stratum additionally records `finrank range(paperTotalMap W B) = r` and
>   `r <= rEdge p`.  The new `nhdsWithin` theorems say the rank-refined
>   certificate holds relative to these strata.
> - **Pen-and-paper check.** The existing certificate already proves
>   `rank(residualBlock p) = rEdge p - finrank U0` whenever the exact rank of
>   edge `p` is supplied.  The basepoint certificate gives
>   `finrank U0 = finrank range(paperTotalMap W B)`, so on the source-shaped
>   stratum this rewrites to `rEdge p - r`.
> - **Proved.** Pointwise rank-stratum membership turns residual-rank
>   implications into residual-rank equalities.  A continuous edge family based
>   at the fixed paper chain gives the rank-refined certificate in a relative
>   neighborhood of the rank stratum.
> - **Assumed.** The same field, finite-dimensional, continuity, and fixed-base
>   hypotheses as the existing product-reduction boundary.  Exact edge ranks and
>   source rank inequalities are stratum restrictions.
> - **Cited.** None.
> - **Deferred.** Exact-rank openness, full source Theorem 3, analytic
>   ideal-germ transport, regular-suspension/RLCT additivity, normal-crossing
>   production, and the final RLCT extraction.
> - **Kill conditions.** Do not read the `nhdsWithin` statements as ambient
>   exact-rank neighborhoods, and do not identify the residual product with a raw
>   product of untransformed lower-right edge blocks.
