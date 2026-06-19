# Statement card - A2 adapted matrix composition

> **Claim.** In any supplied through-subspace adapted basis family, extending a
> chain segment by one edge corresponds to left-multiplying the prefix matrix by
> the adapted edge matrix.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix`,
>   `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedEdgeMatrix`, and
>   `DLNFibre.DLN.Aoyagi.throughSubspaceAdaptedChainMapMatrix_succ`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** The theorem is the matrix form of
>   `chainMap_succ : chainMap i p.succ = A p ∘ chainMap i p.castSucc`.
>   Mathlib's `LinearMap.toMatrix_comp` gives the matrix order
>   `edge * prefix`.
> - **Proved.** A one-step basis-matrix composition identity for arbitrary
>   supplied `ThroughSubspaceChartData`.
> - **Assumed.** Finite and decidable matrix index families for the adapted
>   bases; no rank, chart-open, or endpoint-kernel hypothesis is used.
> - **Cited.** None.
> - **Deferred.** Iterating this recurrence over all edges; connecting the
>   resulting all-layer edge-matrix product with the endpoint block theorem;
>   product-reduction induction; rank/open-neighborhood statements; and every
>   analytic/RLCT consequence.
> - **Kill conditions.** This is functoriality of matrices under composition.
>   It does not say that a product-reduction step has been run or that the edge
>   matrices have any special block form unless combined with the separate edge
>   block theorems.
