# Statement card - A2 product-difference entry-ideal boundary

> **Claim.** From the fixed-base triangular endpoint product-reduction form,
> determinant-unit triangular multiplication carries the endpoint
> product-difference entry ideal to the cleaned four-block ideal
> `<entries(Ctop-I), entries(F2), entries(F3), entries(D)>`, where `D` is the
> deterministic transformed residual product.
>
> - **Lean:**
>   `matrixEntryIdeal_neg_eq`,
>   `matrixEntryIdeal_fromBlocks_eq_fourMatrixEntryIdeal`,
>   `matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_fourMatrixEntryIdeal`
>   in `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`;
>   `matrixEntryIdeal_triangularBlockProductDifference_eq_fourMatrixEntryIdeal`,
>   `PaperEndpointFixedBaseProductDifferenceEntryIdealSourceRanks`,
>   `PaperEndpointFixedBaseTriangularResidualProductSourceRanks.exists_productDifferenceEntryIdeal`,
>   `PaperEndpointFixedBaseTriangularResidualProductSourceRanks.toProductDifferenceEntryIdealSourceRanks`,
>   `paperEndpointFixedBaseProductDifferenceEntryIdeal_selfBase_mem_nhdsWithin_source`,
>   `PaperEndpointProductDifferenceEntryIdealLocalCertificate`, and
>   `exists_paperEndpointProductDifferenceEntryIdealLocalCertificate`
>   in `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`.
> - **Gloss.** The generic algebra says block entries generate the supremum of
>   the four block entry ideals, signs are invisible to entry ideals, and the
>   lower-right correction `F3*F2` is redundant modulo the entries of `F2` and
>   `F3`.  The boundary wrapper applies determinant-unit entry-ideal transport
>   to Aoyagi's triangular endpoint matrices.
> - **Pen-and-paper check.**
>   `reproduction-a2-product-difference-entry-ideal-boundary.md`.
> - **Proved.** A scalar matrix-entry-ideal equality over commutative rings and
>   its fixed-base/source-rank endpoint package as a relative `nhdsWithin`
>   statement over Aoyagi's source-shaped rank stratum.
> - **Assumed.** The existing fixed-base product-reduction certificate supplies
>   the triangular endpoint form and determinant-unit triangular multipliers.
>   The source-rank stratum remains a restriction.
> - **Cited.** None.
> - **Deferred.** Analytic germ-ideal equality, exact-rank openness, Aoyagi
>   Lemma 1 normalization, regular-suspension RLCT additivity,
>   normal-crossing production, pole order, and RLCT extraction.
> - **Kill conditions.** Do not use this as analytic ideal transport.  Do not
>   identify `ChartLocalSuffixState.residualProduct` with a raw product of
>   original lower-right edge blocks without a separate orientation/product
>   theorem.
