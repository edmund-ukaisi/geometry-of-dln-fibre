# Statement card - A2 product-reduction boundary certificate

> **Claim.** The currently proved elementary/topological part of Aoyagi's
> product reduction can be used through a named certificate boundary.  For a
> fixed paper-order base chain `B`, endpoint bases chosen from a complement to
> the total kernel, and a continuous reversed-edge family based at
> `reverseEdge W B`, there is a neighborhood on which recursive determinant
> charts hold, the endpoint product is block-diagonalized by the deterministic
> suffix state, and residual-rank conclusions are available as implications
> from exact pointwise edge-rank hypotheses.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionCertificate`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseProductReductionCertificate_of_recursiveDetCharts`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseProductReductionCertificate_selfBase_mem_nhds`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionLocalCertificate`,
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseProductReductionLocalCertificate_of_isCompl`,
>   `DLNFibre.DLN.Aoyagi.PaperEndpointProductReductionLocalCertificate`, and
>   `DLNFibre.DLN.Aoyagi.exists_paperEndpointProductReductionLocalCertificate`
>   (`lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`).
> - **Gloss.** The fixed-base certificate has three fields: recursive
>   determinant charts, endpoint block diagonalization, and residual-rank
>   implications.  The local fixed-base certificate adds the basepoint adapted
>   coordinate certificate and a neighborhood membership statement.  The
>   existential local certificate chooses the total-kernel complement.
> - **Pen-and-paper check.** This packages the already checked recurrence
>   `M = [I Bprev; 0 I] * E p`,
>   `Bnext = (topLeftCorner M)^-1 * upperRightBlock M`, and adapted residual
>   `schurResidualBlock M`.  It does not replace the residual by a raw
>   lower-right block of the untransformed edge.
> - **Proved.** A pointwise recursive-chart hypothesis constructs the fixed-base
>   product-reduction certificate.  A continuous edge family based at `B`
>   supplies the certificate on a neighborhood.  Finite-dimensional paper chains
>   admit the local certificate after choosing a complement to the total kernel.
> - **Assumed.** Field/vector-space and finite-dimensional hypotheses; normed
>   field and topological vector-space hypotheses for continuous-linear-map
>   coordinates; continuity of the edge family; exact edge ranks only when
>   invoking the residual-rank implications.
> - **Cited.** None.
> - **Deferred.** Exact-rank openness, source target-normalization, the full
>   printed triangular product-reduction theorem from Aoyagi's source
>   hypotheses, analytic ideal-germ transport, regular-suspension/RLCT
>   additivity, normal-crossing extraction, and blow-up certificates.
> - **Kill conditions.** Do not name this as an RLCT theorem, do not use it as
>   Aoyagi Lemma 1, and do not read the residual-rank implications as
>   neighborhood exact-rank assertions.
