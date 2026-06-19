# Statement card - A2 through-layer matrix block

> **Claim.** Transported through-subspace bases give the layer matrix block
> form `[I B; 0 D]`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** For a through-subspace edge
>   `A p : V p.castSucc -> V p.succ`, choose a basis `bU` of the source
>   through-subspace. The target through-subspace basis is the transported
>   basis `bU.map (throughSubspaceEdgeEquiv ...)`. With arbitrary quotient
>   bases extending these subspace bases via `Module.Basis.sumQuot`, the matrix
>   of `A p` has form `fromBlocks 1 B 0 D`.
> - **Proved.** The basis-coordinate bookkeeping: transported bases give the
>   identity top-left block; membership of the transported subspace gives the
>   zero lower-left block.
> - **Assumed.** Finite/decidable source index types for `LinearMap.toMatrix`,
>   a finite target quotient index, and explicit bases of the source
>   through-subspace and the two quotient spaces. The quotient bases are
>   inputs, not constructed here.
> - **Cited.** None.
> - **Deferred.** Packaging simultaneous compatible bases for every layer;
>   translating the source-to-target Lean orientation back to Aoyagi's
>   paper-order matrices; connecting this block-form corollary to the
>   chart-local product-reduction identity; full Aoyagi Theorem 3; and every
>   analytic/RLCT consequence.
> - **Kill conditions.** Arbitrary adapted bases give `[C B; 0 D]` with
>   invertible `C`, not necessarily `[I B; 0 D]`. The identity corner requires
>   transported through-subspace bases. This is still not a fixed-coordinate
>   chart theorem.
