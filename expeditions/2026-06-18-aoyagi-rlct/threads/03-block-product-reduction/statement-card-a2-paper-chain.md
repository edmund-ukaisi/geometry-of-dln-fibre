# Statement card - A2 paper-order chain

> **Claim.** Aoyagi's descending paper-order matrix product has a Lean
> composite with the expected identity, one-edge, transitivity, and
> prefix/suffix split laws.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.paperChainMap`,
>   `DLNFibre.DLN.Aoyagi.paperChainMap_self`,
>   `DLNFibre.DLN.Aoyagi.paperChainMap_succ`,
>   `DLNFibre.DLN.Aoyagi.paperChainMap_edge`,
>   `DLNFibre.DLN.Aoyagi.paperChainMap_trans`,
>   and
>   `DLNFibre.DLN.Aoyagi.paperChainMap_zero_last_eq_prefix_comp_suffix`,
>   plus `DLNFibre.DLN.Aoyagi.reverseVertex`,
>   `DLNFibre.DLN.Aoyagi.reverseEdge`,
>   `DLNFibre.DLN.Aoyagi.reverseEdge_eq_paperChainMap`, and
>   `DLNFibre.DLN.Aoyagi.chainMap_reverse_eq_paper`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean`).
> - **Gloss.** For paper-order maps `B p : W p.succ -> W p.castSucc`,
>   `paperChainMap W B i j hij : W j -> W i` is the ordered descending
>   composite from layer `j` down to layer `i`. Extending the upper endpoint
>   composes the new paper edge on the right, matching the displayed product
>   order `A^(1) ... A^(L) : W_(L+1) -> W_1`.
> - **Proved.** The empty composite is the identity, the one-edge composite is
>   the given edge, composites split at an intermediate vertex, and the full
>   product splits as paper prefix followed by paper suffix. Also proved:
>   after reversing vertices, the source-to-target `chainMap` is exactly the
>   corresponding paper-order `paperChainMap`.
> - **Assumed.** Field-vector-space chain and paper-order linear maps. No rank,
>   chart, topology, or analytic hypotheses.
> - **Cited.** None.
> - **Deferred.** Transferring the finite adapted-basis block corollaries into
>   paper-order notation; determinant/open-chart wrappers; the product
>   reduction induction; and every analytic/RLCT consequence.
> - **Kill conditions.** This is only product-order bookkeeping. It does not
>   prove Aoyagi Theorem 3, rank preservation, fixed-chart invertibility, or
>   any normal-crossing/RLCT statement.
