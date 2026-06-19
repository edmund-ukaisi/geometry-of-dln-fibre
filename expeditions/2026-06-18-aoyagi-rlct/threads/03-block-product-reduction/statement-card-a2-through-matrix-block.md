# Statement card - A2 through-layer matrix block

> **Claim.** Transported through-subspace bases give the layer matrix block
> form `[I B; 0 D]`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero`
>   and
>   `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_basisOfIsCompl_eq_fromBlocks_one_zero`
>   and
>   `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_prefix_basisOfIsCompl_eq_fromBlocks_one_zero`
>   and
>   `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero`
>   and
>   `DLNFibre.DLN.Aoyagi.exists_unitriangular_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** For a through-subspace edge
>   `A p : V p.castSucc -> V p.succ`, choose a basis `bU` of the source
>   through-subspace. The target through-subspace basis is the transported
>   basis `bU.map (throughSubspaceEdgeEquiv ...)`. With arbitrary quotient
>   bases extending these subspace bases via `Module.Basis.sumQuot`, the matrix
>   of `A p` has form `fromBlocks 1 B 0 D`. Equivalently, if complements
>   `W` and `W'` are supplied and the ambient bases are built from
>   `basisOfIsCompl`, the same block form holds in direct-sum adapted bases.
>   A prefix-transported variant uses one initial basis of `U₀` and transports
>   it to both adjacent through-subspaces by `throughSubspacePrefixEquiv`.
>   `ThroughSubspaceChartData` bundles supplied complements and complement
>   bases for every layer, and the bundled unitriangular corollary says the
>   transformed edge matrix remains in some identity-corner chart form.
>   Finite-dimensional construction of such supplied data is tracked in the
>   separate chart-data existence card.
> - **Proved.** The basis-coordinate bookkeeping: transported bases give the
>   identity top-left block; transported subspace coordinates give the zero
>   lower-left block. The direct-sum version uses
>   `Submodule.prodEquivOfIsCompl` to build the ambient adapted bases. The
>   prefix variant proves the adjacent top bases are compatible with one common
>   initial through-basis. The chart-data variants remove repeated local
>   arguments; the separate finite chart-data theorem supplies one concrete
>   choice of complements and bases under finite-dimensional hypotheses.
> - **Assumed.** Finite/decidable source index types for `LinearMap.toMatrix`,
>   a finite target quotient/complement index, explicit bases of the source
>   through-subspace, and either quotient bases or complement bases. In the
>   bundled version, the complement subspaces and complement bases are still
>   inputs.
> - **Cited.** None.
> - **Deferred.** Translating the source-to-target Lean orientation back to
>   Aoyagi's paper-order matrices; expressing the paper-side rank/open-chart
>   hypotheses against the finite chart-data construction; running the
>   chart-local product-reduction induction; full Aoyagi Theorem 3; and every
>   analytic/RLCT consequence.
> - **Kill conditions.** Arbitrary adapted bases give `[C B; 0 D]` with
>   invertible `C`, not necessarily `[I B; 0 D]`. The identity corner requires
>   transported through-subspace bases. This is still not a fixed-coordinate
>   chart theorem.
