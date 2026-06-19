# Statement card - A2 recursive Bprev block-diagonal neighborhood

> **Claim.** In endpoint bases fixed from a base chain `B`, a continuous
> reversed-edge family based at `reverseEdge W B` has a neighborhood on which
> the endpoint product is block-diagonalized by the deterministic recursive
> suffix state.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrixOfReverseEdges`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseEdgeMatrixOfReverseEdges`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseTotalMatrixOfReverseEdges`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_recursiveBprev_blockDiagonal_mem_nhds`,
>   and
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_mem_nhds`
>   (`lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`).
> - **Gloss.** The topology theorem supplies determinant charts only for the
>   actual accumulated upper blocks produced by `ChartLocalSuffixState`; the
>   pointwise endpoint theorem therefore uses
>   `ChartLocalSuffixState.suffixState_blockDiagonal` directly, not the older
>   all-`Bprev` fixed-base wrapper.
> - **Pen-and-paper check.** The recurrence is
>   `M = [I Bprev; 0 I] * E p` and
>   `Bnext = (topLeftCorner M)^-1 * upperRightBlock M`. At the base family
>   `E p = reverseEdge W B p`, the transformed determinant chart follows from
>   the endpoint unitriangular identity-corner theorem with `F = -Bprev`, since
>   `paperEndpointUnitriangularLeft F = [I -F; 0 I]`.
> - **Proved.** Under recursive determinant-chart hypotheses, the deterministic
>   suffix state block-diagonalizes the endpoint fixed-base product. If the
>   edge family is continuous at the base parameter and equals `reverseEdge W B`
>   there, those recursive charts hold at the base parameter and the endpoint
>   block form holds on a neighborhood.
> - **Assumed.** Normed-field topology and finite-dimensional endpoint bases
>   for continuous-linear-map coordinates; continuity of the edge family.
> - **Cited.** None.
> - **Deferred.** Exact-rank neighborhoods, certificate transport, the full
>   source-facing Theorem 3 statement, and continuity of `L`, `Ctop`, and `D`
>   unless later certificate packaging requires those fields.
> - **Kill conditions.** Do not read this as proving rank strata are open, as
>   transporting exact-rank certificates, or as proving the RLCT regular
>   variable contribution.
