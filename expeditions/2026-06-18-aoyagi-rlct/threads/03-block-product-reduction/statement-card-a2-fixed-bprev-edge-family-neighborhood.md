# Statement card - A2 fixed-Bprev edge-family neighborhood

> **Claim.** Fix the endpoint bases coming from a base paper-order chain `B`
> and fix a prescribed family of accumulated upper blocks `Bprev p`. Then the
> set of continuous reversed-edge families whose fixed-basis coordinate matrices
> satisfy all transformed determinant-chart predicates
> `[I Bprev p; 0 I] * M_p` is a neighborhood of the base edge family in the
> finite Pi/product topology.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_selfBase_mem_nhds_transformed_identityCornerDetChart`
>   (`lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`), using
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart`.
> - **Gloss.** This is the finite-intersection step from one-edge neighborhoods
>   to an edge-family neighborhood. The family `Bprev` is supplied before the
>   neighborhood is formed.
> - **Proved.** For every fixed family `Bprev : ∀ p, Matrix ...`, the
>   conjunction over all `p : Fin N` of the transformed determinant-chart
>   predicates is a neighborhood of
>   `fun p => LinearMap.toContinuousLinearMap (reverseEdge W B p)`.
> - **Assumed.** Finite-dimensional paper-order layers, a supplied complement
>   `U0` to the base total kernel, a nontrivially normed complete field, and
>   topological-vector-space structures on the layers.
> - **Cited.** None.
> - **Deferred.** No continuity of the `Bprev` produced by the suffix-chain
>   induction is proved here. Exact rank strata, source-faithful chain
>   neighborhoods, regular coordinate-change certificates, and RLCT
>   consequences remain separate.
> - **Kill conditions.** Do not use this as a neighborhood that works for all
>   possible accumulated upper blocks. Do not feed it directly into the
>   all-layer chart-local induction without a bridge explaining which fixed
>   finite `Bprev` family is being controlled.
