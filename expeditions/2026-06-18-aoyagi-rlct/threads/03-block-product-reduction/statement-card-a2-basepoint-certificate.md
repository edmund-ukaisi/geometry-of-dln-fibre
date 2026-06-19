# Statement card - A2 endpoint basepoint certificate

> **Claim.** A finite-dimensional fixed paper-order chain admits an
> endpoint-compatible basepoint certificate: choose a complement to the total
> product kernel; in the resulting adapted endpoint coordinates, each basepoint
> edge has identity-corner form, determinant-chart neighborhoods exist for the
> edge and its upper-unitriangular transforms, residual lower-right edge ranks
> are the source edge ranks minus the through-rank, and the total product has
> endpoint block form with suffix-chain right elimination.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.paperTotalMap`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointChartData`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointAdaptedEdgeMatrix`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointAdaptedTotalMatrix`,
>   `DLNFibre.DLN.Aoyagi.lowerRightBlock_throughSubspaceEndpointAdaptedEdgeMatrix_rank_eq_sub`,
>   `DLNFibre.DLN.Aoyagi.lowerRightBlock_paperEndpointAdaptedEdgeMatrix_rank_eq_sub`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointAdaptedTotalMatrix_eq_fromBlocks_one_zero_zero`,
>   `DLNFibre.DLN.Aoyagi.productReduction_paperEndpointAdaptedTotalMatrix_suffixChain_rightElim`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointBasepointCertificate`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointBasepointCertificate_of_isCompl`,
>   and
>   `DLNFibre.DLN.Aoyagi.exists_paperEndpointBasepointCertificate`
>   (`lean/DLNFibre/DLN/Aoyagi/BasepointCertificate.lean`).
> - **Gloss.** This packages the endpoint-compatible chart data rather than the
>   ordinary per-edge complement chart. The new endpoint residual-rank theorem
>   repeats the Schur-rank argument in the endpoint `Fin`-indexed chart, so all
>   fields refer to one fixed adapted basis family for the chosen base chain.
> - **Proved.** Pure finite-dimensional linear algebra and determinant-chart
>   topology at the fixed basepoint.
> - **Assumed.** Field-vector-space hypotheses, finite-dimensional paper-order
>   layers, topological ring/open-units hypotheses for neighborhood fields, and
>   either a supplied total-kernel complement or the classical chosen complement
>   in the existential theorem.
> - **Cited.** None.
> - **Deferred.** Fixed-coordinate variable-chain families, exact rank-stratum
>   hypotheses for nearby layers, regular coordinate-change certificates, finite
>   atlas coverage, normal-crossing extraction, and RLCT consequences.
> - **Review.** Built and axiom-audited by the controller. Xhigh subagent
>   reviews recommended this exact basepoint-only boundary and warned against
>   re-adapting bases across a neighborhood.
> - **Kill conditions.** Do not read this as Aoyagi Theorem 3. It gives no
>   canonical or `B`-independent bases, no continuous dependence of bases on the
>   chain, and no open exact-rank stratum.
