# Statement card - A2 triangular block diagonal form

> **Claim.** The deterministic endpoint block-diagonal certificate can be
> restated with Aoyagi Theorem 3-style triangular endpoint multipliers:
> a regular lower unitriangular left multiplier `[I 0; F3 I]` and a regular
> upper unitriangular right multiplier `[I F2; 0 I]`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.lowerUnitriangular_mul_fromBlocks_one_zero_indexed`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step_L_eq_lowerUnitriangular`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_L_eq_lowerUnitriangular`,
>   `DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal`,
>   `DLNFibre.DLN.Aoyagi.productReduction_chartLocal_suffixChain_triangularBlockDiagonal_indexed`,
>   and
>   `DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal`.
> - **Gloss.** The endpoint certificate already has
>   `S.L * total * [I -S.B; 0 I] = [S.Ctop 0; 0 S.D]`.  The new invariant
>   proves `S.L = [I 0; F3 I]`, so the source-facing right multiplier is
>   obtained by choosing `F2 = -S.B`.
> - **Proved.** Products of lower unitriangular blocks stay lower
>   unitriangular; the deterministic suffix state has lower-unitriangular
>   `L`; the abstract suffix-chain theorem and the fixed-base certificate now
>   expose triangular multipliers.  The stated triangular multipliers and
>   `Ctop` have determinant units.
> - **Assumed.** The same hypotheses as the existing recursive fixed-base
>   product-reduction certificate: finite block index types, endpoint bases
>   fixed from a total-kernel complement, and recursive determinant-chart
>   hypotheses already packaged in the certificate.
> - **Cited.** None.
> - **Review.** xhigh reviewer `Kepler` passed the Lean/math audit; see
>   `review-a2-triangular-block-diagonal.md`.
> - **Deferred.** Chart coverage from only source rank hypotheses, exact-rank
>   openness, analytic ideal-germ transport, Aoyagi Lemma 1, regular-variable
>   RLCT bookkeeping, normal-crossing extraction, and all final RLCT claims.
> - **Kill conditions.** Do not identify `D` with an untransformed raw
>   lower-right product, and do not read this theorem as an open-neighborhood
>   or RLCT statement.
