# Statement card - A2 through-layer matrix block

> **Claim.** Transported through-subspace bases give the layer matrix block
> form `[I B; 0 D]`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero`
>   and
>   `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_basisOfIsCompl_eq_fromBlocks_one_zero`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** For a through-subspace edge
>   `A p : V p.castSucc -> V p.succ`, choose a basis `bU` of the source
>   through-subspace. The target through-subspace basis is the transported
>   basis `bU.map (throughSubspaceEdgeEquiv ...)`. With arbitrary quotient
>   bases extending these subspace bases via `Module.Basis.sumQuot`, the matrix
>   of `A p` has form `fromBlocks 1 B 0 D`. Equivalently, if complements
>   `W` and `W'` are supplied and the ambient bases are built from
>   `basisOfIsCompl`, the same block form holds in direct-sum adapted bases.
> - **Proved.** The basis-coordinate bookkeeping: transported bases give the
>   identity top-left block; transported subspace coordinates give the zero
>   lower-left block. The direct-sum version uses
>   `Submodule.prodEquivOfIsCompl` to build the ambient adapted bases.
> - **Assumed.** Finite/decidable source index types for `LinearMap.toMatrix`,
>   a finite target quotient/complement index, explicit bases of the source
>   through-subspace, and either quotient bases or complement bases. The
>   complements and bases are inputs, not constructed here.
> - **Cited.** None.
> - **Deferred.** Packaging simultaneous compatible bases for every layer;
>   proving total-product block form; translating the source-to-target Lean
>   orientation back to Aoyagi's paper-order matrices; connecting this
>   block-form corollary to the chart-local product-reduction identity; full
>   Aoyagi Theorem 3; and every analytic/RLCT consequence.
> - **Kill conditions.** Arbitrary adapted bases give `[C B; 0 D]` with
>   invertible `C`, not necessarily `[I B; 0 D]`. The identity corner requires
>   transported through-subspace bases. This is still not a fixed-coordinate
>   chart theorem.
