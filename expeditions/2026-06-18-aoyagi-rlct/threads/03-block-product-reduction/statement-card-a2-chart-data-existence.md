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
>   and
>   `DLNFibre.DLN.Aoyagi.exists_isCompl_ker_throughSubspaceChartDataOfFiniteDimensional`
>   (`lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`).
> - **Gloss.** For a chosen initial through-subspace `U0`, the construction
>   chooses a complement to each transported through-subspace, indexes that
>   complement by `Fin (Module.finrank K ...)`, and uses `Module.finBasis` to
>   build `ThroughSubspaceChartData`. The kernel-complement theorem also
>   chooses `U0` complementary to the total kernel and carries the equality
>   `finrank K U0 = finrank K (LinearMap.range P)`.
> - **Proved.** Existence of concrete finite-indexed supplied chart data from
>   finite-dimensional layer hypotheses, using only elementary complement
>   existence and finite-dimensional bases.
> - **Assumed.** Field-vector-space hypotheses and
>   `[∀ j, FiniteDimensional K (V j)]`. The construction is noncomputable and
>   makes arbitrary complement and basis choices.
> - **Cited.** None.
> - **Deferred.** Translating this source-to-target Lean construction back to
>   Aoyagi's paper-order matrices; expressing the paper-side rank/open-chart
>   hypotheses against these coordinates; running the chart-local
>   product-reduction induction; and all analytic/RLCT consequences.
> - **Kill conditions.** This is not a fixed-coordinate chart theorem. Product
>   rank alone does not make preselected top-left layer blocks invertible; the
>   identity corner comes from transported through-bases and chosen adapted
>   coordinates.
