# Statement card - A2 recursive Bprev topology

> **Claim.** The accumulated upper block `Bprev` produced by the deterministic
> suffix recursion is continuous at a base parameter, and therefore the
> transformed determinant charts persist in a fixed-base neighborhood when the
> basepoint recursive chart hypotheses hold.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.continuousAt_matrix_inv_of_isUnit_det`,
>   `DLNFibre.DLN.Aoyagi.continuousAt_chartLocalSuffixState_step_B`,
>   `DLNFibre.DLN.Aoyagi.continuousAt_chartLocalSuffixState_suffixState_B`
>   (`lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`), and
>   `DLNFibre.DLN.Aoyagi.paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart`
>   (`lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`).
> - **Gloss.** The one-step update for `B` is
>   `Bnext = (topLeftCorner M)^-1 * upperRightBlock M`. The topology proof uses
>   continuity of matrix multiplication, block projections, and matrix inverse
>   at a unit determinant, then iterates the one-step result along
>   `ChartLocalSuffixState.suffixState`.
> - **Proved.** If the edge family is continuous at the base parameter and all
>   recursively transformed edges lie in the determinant chart at that base
>   parameter, then each recursively produced `Bprev` block is continuous at the
>   base parameter. In fixed endpoint bases, the determinant-chart conditions
>   then hold on a neighborhood for the actual recursive `Bprev` family.
>   The endpoint block-diagonal use of this neighborhood is recorded separately
>   in
>   `statement-card-a2-recursive-bprev-block-diagonal-neighborhood.md`.
> - **Assumed.** Normed-field topology, complete spaces for fixed-basis
>   continuous-linear-map coordinates, finite block index types, continuity of
>   the edge family, and determinant-chart hypotheses for the basepoint
>   recursively transformed edges.
> - **Cited.** None.
> - **Deferred.** Exact-rank neighborhoods, certificate transport, the full
>   source-facing Theorem 3 statement, and continuity of `L`, `Ctop`, and `D`
>   if later certificates require those fields.
> - **Kill conditions.** Do not read this as proving exact-rank strata are open
>   or as proving the full product-reduction coordinate certificate.
