# Statement card - A2 deterministic suffix-state step

> **Claim.** The chart-local suffix induction has a deterministic one-step
> state update. If a suffix state already block-diagonalizes the tail, and the
> transformed next edge `[I Bprev; 0 I] * E p` lies in the determinant chart,
> then the state obtained by
> `Bnext = (topLeftCorner M)^-1 * upperRightBlock M` block-diagonalizes the
> longer suffix.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.BlockDiagonal`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.transformedEdge`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step`,
>   and
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step_blockDiagonal`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`).
> - **Gloss.** This makes explicit the witness that the older existential
>   suffix-chain proof was already passing forward. The transformed edge is
>   `M = [I Bprev; 0 I] * E p`; the next right-elimination block is the Schur
>   right-elimination block of `M`.
> - **Proved.** One deterministic step preserves the block-diagonal invariant
>   under the recursive determinant-chart hypothesis for the transformed edge.
> - **Assumed.** Commutative ring coefficients, finite block index types, the
>   suffix composition law `P(p.castSucc,j) = P(p.succ,j) * E p`, the previous
>   block-diagonal invariant, and the determinant-chart hypothesis for the
>   transformed edge.
> - **Cited.** None.
> - **Deferred.** The full deterministic recursive suffix-chain state from an
>   endpoint `j` down to an initial index `i`, continuity of that recursive
>   state, source-faithful chain neighborhoods, exact rank strata, regular
>   coordinate-change certificates, and RLCT consequences.
> - **Kill conditions.** Do not read the one-step theorem as a completed
>   recursive construction or as a proof that the recursive chart hypotheses
>   hold on a neighborhood.
