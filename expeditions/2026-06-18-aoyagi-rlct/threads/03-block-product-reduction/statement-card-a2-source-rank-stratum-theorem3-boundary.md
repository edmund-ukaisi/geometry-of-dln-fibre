# Statement card - A2 source-rank-stratum Theorem 3 boundary

> **Claim.** At a fixed base chain and on Aoyagi's source-shaped rank stratum,
> the proved product-reduction boundary can be packaged in the source shape:
> triangular endpoint multipliers put the total product in block-diagonal form
> with lower-right block equal to the deterministic transformed residual
> product, and each visited residual block has rank `rEdge p - r`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseTriangularResidualProductSourceRanks`
>   and
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct_sourceRanks`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`).
> - **Gloss.** The endpoint lower-right block is
>   `ChartLocalSuffixState.residualProduct` for the transformed Schur residuals
>   visited by the suffix recursion.  The source rank stratum supplies the base
>   product rank `r`, exact nearby layer ranks `rEdge`, and the inequalities
>   `r <= rEdge p`.
> - **Pen-and-paper check.** Aoyagi's Lemma 2 gives the Schur residual update;
>   iterating through Theorem 3 gives the transformed residual product.  The
>   existing residual-rank implication gives
>   `rank(residualBlock p) = rEdge p - finrank(U0)`, and the fixed-base
>   basepoint certificate rewrites `finrank(U0)` to the source rank `r`.
> - **Proved.** A bundled fixed-base/source-stratum endpoint conclusion from
>   the existing triangular residual-product endpoint theorem and the existing
>   source-rank residual-block theorem.
> - **Assumed.** The same field, finite-dimensional, fixed-base, and certificate
>   hypotheses as the existing product-reduction boundary.  Membership in the
>   source rank stratum is a restriction, not an openness theorem.
> - **Cited.** None.
> - **Deferred.** Full source Theorem 3, Aoyagi Lemma 1 normalization, analytic
>   ideal-germ transport, regular-suspension/RLCT additivity, normal-crossing
>   production, pole order, and the final RLCT extraction.
> - **Kill conditions.** Do not read this as exact-rank openness or as a
>   neighborhood theorem beyond the existing `nhdsWithin` boundary. Do not
>   identify the residual product with a raw product of untransformed edge
>   blocks.
