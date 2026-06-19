# Statement card - A2 finite chart-data existence

> **Claim.** In finite-dimensional field-vector-space chains, one can choose
> finite-indexed complement and basis data for the transported through-subspaces.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.throughSubspaceComplement`,
>   `DLNFibre.DLN.Aoyagi.throughSubspace_isCompl_complement`,
>   `DLNFibre.DLN.Aoyagi.throughSubspaceComplementIndex`,
>   `DLNFibre.DLN.Aoyagi.throughSubspaceChartDataOfFiniteDimensional`,
>   `DLNFibre.DLN.Aoyagi.nonempty_throughSubspaceChartDataOfFiniteDimensional`,
>   `DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`,
>   `DLNFibre.DLN.Aoyagi.exists_unitriangular_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`,
>   `DLNFibre.DLN.Aoyagi.toMatrix_chainMap_zero_last_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`,
>   and
>   `DLNFibre.DLN.Aoyagi.exists_isCompl_ker_throughSubspaceChartDataOfFiniteDimensional`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** For a chosen initial through-subspace `U0`, the construction
>   chooses a complement to each transported through-subspace, indexes that
>   complement by `Fin (Module.finrank K ...)`, and uses `Module.finBasis` to
>   build `ThroughSubspaceChartData`. The kernel-complement theorem also
>   chooses `U0` complementary to the total kernel and carries the equality
>   `finrank K U0 = finrank K (LinearMap.range P)`. The concrete edge and
>   endpoint corollaries instantiate the existing block-form theorems with
>   these chosen complements and `Module.finBasis` bases.
> - **Proved.** Existence of concrete finite-indexed supplied chart data from
>   finite-dimensional layer hypotheses, using only elementary complement
>   existence and finite-dimensional bases; concrete finite-basis versions of
>   the per-edge `[I B; 0 D]`, unitriangular chart-preservation, and endpoint
>   `[I 0; 0 0]` block statements.
> - **Assumed.** Field-vector-space hypotheses and
>   `[∀ j, FiniteDimensional K (V j)]`. The construction is noncomputable and
>   makes arbitrary complement and basis choices.
> - **Cited.** None.
> - **Deferred.** Expressing the paper-side rank/open-chart hypotheses against
>   these coordinates; running the chart-local
>   product-reduction induction; and all analytic/RLCT consequences.
> - **Kill conditions.** This is not a fixed-coordinate chart theorem. Product
>   rank alone does not make preselected top-left layer blocks invertible; the
>   identity corner comes from transported through-bases and chosen adapted
>   coordinates.
