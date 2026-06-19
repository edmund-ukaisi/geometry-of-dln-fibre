# Statement card - A2 paper endpoint suffix-chain right elimination

> **Claim.** In Aoyagi paper order, after reversing the chain and using the
> endpoint-compatible finite adapted chart data, the adapted matrix of the full
> paper product admits suffix-chain right elimination.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.productReduction_paperChainMap_endpointChartData_suffixChain_rightElim`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** For paper-order maps `B p : W p.succ -> W p.castSucc`, the
>   theorem applies the supplied suffix-chain reduction to
>   `(reverseVertex W) (reverseEdge W B)`. If `U0` complements the kernel of the
>   total paper product, the endpoint-compatible finite chart data gives adapted
>   bases at every reversed layer. In those bases, there exist `Bmat` and `Dmat`
>   such that the matrix of the total `paperChainMap`, multiplied on the source
>   side by `[I -Bmat; 0 I]`, equals `[I 0; 0 Dmat]`.
> - **Proved.** A paper-order wrapper around the already proved supplied
>   through-subspace suffix-chain theorem, using `chainMap_reverse_eq_paper` and
>   the endpoint-compatible chart data construction.
> - **Assumed.** Field-vector-space hypotheses, finite-dimensional paper-order
>   layers, and an explicit complement `IsCompl U0 (ker totalPaperProduct)`.
> - **Cited.** None.
> - **Deferred.** Fixed coordinate charts over a neighborhood, openness of the
>   determinant/rank chart, regular coordinate changes, identification with
>   Aoyagi's named residual factors, and every analytic/RLCT consequence.
> - **Review.** Build-checked by the controller. Xhigh review confirmed the
>   reversal orientation and statement scope, with the source-fidelity boundary
>   below.
> - **Kill conditions.** This is still pointwise adapted-coordinate
>   bookkeeping. The bases and complements are chosen from the actual chain; the
>   theorem does not assert a source-faithful local chart theorem.
