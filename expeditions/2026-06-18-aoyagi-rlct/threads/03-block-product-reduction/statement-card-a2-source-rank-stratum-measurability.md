# Statement card - A2 source-rank stratum measurability

> **Claim.** Aoyagi's fixed-base exact edge-rank stratum, and hence the
> source-shaped rank stratum, is measurable when the finite-basis coordinate
> matrices of the edge family vary continuously.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.measurableSet_matrix_rank_eq_of_continuous`
>   (`lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`),
>   `DLNFibre.DLN.Aoyagi.measurableSet_paperEndpointFixedBaseEdgeRankStratum_of_continuous`,
>   and
>   `DLNFibre.DLN.Aoyagi.measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`).
> - **Gloss.** The proof reduces exact rank to rank inequalities, expresses
>   rank inequalities by vanishing of finite minors, and uses closed zero loci
>   of determinant functions.  The source-shaped stratum differs from the edge
>   stratum only by constant base-rank and source-inequality propositions.
> - **Pen-and-paper check.** If all `(q+1)`-minors vanish, then `rank <= q`;
>   otherwise independent rows and then independent columns produce a nonzero
>   `(q+1)`-minor.  Exact rank is the measurable difference
>   `{rank <= q+1} \\ {rank <= q}`.
> - **Proved.** Closedness of finite matrix `rank <= q` loci, measurability of
>   exact-rank loci for continuous finite matrix families, measurability of
>   the fixed-base edge-rank stratum from continuous coordinate matrices, and
>   the source-shaped stratum wrapper.
> - **Assumed.** Field-linear finite-dimensional source spaces, the existing
>   topological vector-space hypotheses, and continuous finite-basis coordinate
>   matrices, or globally continuous `Cedge`.
> - **Cited.** None.
> - **Deferred.** Measurability from only local continuity at a basepoint,
>   exact-rank openness, product-chart construction, original-loss comparison,
>   density/Jacobian transport, residual positivity and integrability,
>   normal-crossing production, pole order, and RLCT extraction.
> - **Kill conditions.** Do not read this as an ambient neighborhood theorem.
>   It supplies a measurable restriction set for local measure handoffs under
>   continuity hypotheses only.
