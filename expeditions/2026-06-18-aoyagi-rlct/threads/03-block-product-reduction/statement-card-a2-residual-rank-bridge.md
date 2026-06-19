# Statement card - A2 residual rank bridge

> **Claim.** In adapted paper-order coordinates, the residual lower-right block
> of one edge has rank equal to the source edge rank minus the through-rank.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.rank_toMatrix_eq_finrank_range`,
>   `DLNFibre.DLN.Aoyagi.rank_schurComplement_eq_sub_rank_fromBlocks`
>   (`lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`), and
>   `DLNFibre.DLN.Aoyagi.lowerRightBlock_paperAdaptedReverseEdgeMatrix_rank_eq_sub`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** Matrix rank is invariant under choice of bases for a linear map.
>   Since an adapted paper edge has identity-corner block form, the A1
>   Schur-complement rank formula applies with top-left block `I`, so the
>   lower-right block has rank
>   `finrank range(reverseEdge W B p) - finrank U0`.
> - **Proved.** Pure finite-dimensional linear algebra over a field.
> - **Assumed.** Finite-dimensional layers for the paper adapted-edge wrapper.
> - **Cited.** None.
> - **Deferred.** Source paper-layer labels, exact rank-stratum packaging,
>   fixed-coordinate chart families for nearby variable layers, and every
>   analytic/RLCT consequence.
> - **Kill conditions.** This is not an openness result for exact rank. It does
>   not say product rank alone chooses fixed coordinate pivots.
