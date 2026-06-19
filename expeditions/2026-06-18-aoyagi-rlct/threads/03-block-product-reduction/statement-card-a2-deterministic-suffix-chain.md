# Statement card - A2 deterministic suffix-chain state

> **Claim.** The chart-local suffix induction has a deterministic recursive
> state. Starting from the terminal state at endpoint `j` and iterating the
> one-step update downward to `i` gives a state whose fields block-diagonalize
> the whole suffix, provided each actually transformed edge lies in the
> determinant chart.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.terminal`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_self`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.terminal_blockDiagonal`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_castSucc`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_blockDiagonal`,
>   and the wrapper
>   `DLNFibre.DLN.Aoyagi.productReduction_chartLocal_suffixChain_blockDiagonal_indexed`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`).
> - **Gloss.** The state
>   `suffixState E j i hij` carries the recursively produced left multiplier,
>   accumulated right-elimination block `B`, top block, and residual block.
>   Its predecessor equation is
>   `suffixState E j p.castSucc _ = step E p (suffixState E j p.succ _)`.
> - **Proved.** The recursive state block-diagonalizes the suffix under
>   determinant-chart hypotheses for the actual transformed edges
>   `transformedEdge E p (suffixState E j p.succ hpj)`. The older existential
>   suffix-chain theorem now extracts its witnesses from this deterministic
>   state.
> - **Assumed.** Commutative ring coefficients, finite block index types, the
>   suffix composition law `P(p.castSucc,j) = P(p.succ,j) * E p`, proof
>   irrelevance for the order proof carried by `P`, terminal empty-suffix law
>   `P j j le_rfl = 1`, and determinant-chart hypotheses for the recursively
>   transformed edges.
> - **Cited.** None.
> - **Deferred.** Continuity of the recursively produced state fields,
>   source-faithful neighborhoods where the recursive chart hypotheses hold,
>   exact rank strata, regular coordinate-change certificates, and RLCT
>   consequences.
> - **Kill conditions.** Do not read the recursive algebra theorem as a
>   topological neighborhood theorem or as proof that exact-rank conditions are
>   open.
