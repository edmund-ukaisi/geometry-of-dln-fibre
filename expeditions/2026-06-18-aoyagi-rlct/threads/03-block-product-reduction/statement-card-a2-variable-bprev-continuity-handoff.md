# Statement card - A2 variable-Bprev continuity handoff

> **Claim.** In fixed endpoint bases, if a parameterized continuous reversed-edge
> family and a parameterized family of accumulated upper blocks `Bprev` are
> continuous at a parameter `x0`, and all transformed determinant-chart
> predicates hold at `x0`, then they hold on a neighborhood of `x0`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_variableBprev_mem_nhds_transformed_identityCornerDetChart`
>   (`lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`).
> - **Gloss.** This is a continuity handoff for supplied variable chart data.
>   It pulls back the open determinant chart along the map
>   `x ↦ [I Bprev x p; 0 I] * M(Cedge x p)` and intersects over `p : Fin N`.
> - **Proved.** For any topological parameter space, continuity at `x0` of the
>   edge family and the supplied `Bprev` family implies neighborhood persistence
>   of all transformed determinant-chart predicates that hold at `x0`.
> - **Assumed.** Finite-dimensional paper-order layers, a supplied complement
>   `U0` to the base total kernel, a nontrivially normed complete field,
>   topological-vector-space structures on the layers, and continuity of the
>   supplied edge and `Bprev` families at the parameter.
> - **Cited.** None.
> - **Deferred.** The theorem does not construct the `Bprev` family produced by
>   the suffix-chain induction and does not prove that recursive family is
>   continuous. Exact rank strata, source-faithful chain neighborhoods, regular
>   coordinate-change certificates, and RLCT consequences remain separate.
> - **Kill conditions.** Do not read this as a non-circular proof that the
>   induction-produced charts exist near the basepoint. It applies only after a
>   concrete continuous `Bprev` family has been supplied.
